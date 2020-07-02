// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
/// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module axi_xbar #(
  /// Number of slave ports of the crossbar.
  /// This many master modules are connected to it.
  parameter int unsigned NumSlvPorts = 32'd0,
  /// Number of master ports of the crossbar.
  /// This many slave modules are connected to it.
  parameter int unsigned NumMstPorts = 32'd0,
  /// Maximum number of transactions each master connected to a slave port of the crossbar can have
  /// in flight at the same time.
  parameter int unsigned MaxMstTrans = 32'd8,
  /// Maximum number of transactions each slave connected to a master port of the crossbar can have
  /// in flight at the same time.
  parameter int unsigned MaxSlvTrans = 32'd8,
  /// Determine if the internal FIFOs of the crossbar are instantiated in fallthrough mode.
  parameter bit FallThrough = 1'b0,
  /// The Latency mode of the xbar. This determines if the channels on the ports have
  /// a spill register instantiated.
  /// Example configurations are provided with the enum `axi_pkg::xbar_latency_e`.
  parameter axi_pkg::xbar_latency_e LatencyMode = axi_pkg::CUT_ALL_AX,
  /// This is the number of `axi_multicut` stages instantiated in the line cross of the channels.
  /// Having multiple stages can potentially add a large number of FFs!
  parameter int unsigned PipelineStages = 32'd0,
  /// AXI ID width of the slave ports. The ID width of the master ports is determined
  /// automatically. See `axi_mux` for details.
  parameter int unsigned AxiIdWidthSlvPorts = 32'd0,
  /// The used ID portion to determine if a different slave is used for the same ID.
  /// See `axi_demux` for details.
  parameter int unsigned AxiIdUsedSlvPorts = 32'd0,
  /// AXI4+ATOP address field width.
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// AXI4+ATOP data field width.
  parameter int unsigned AxiDataWidth = 32'd0,
  /// The number of address rules defined for routing of the transactions.
  /// Each master port can have multiple rules, should have however at least one.
  /// If a transaction can not be routed, the xbar will answer with an `axi_pkg::RESP_DECERR`.
  parameter int unsigned NumAddrRules = 32'd0,
  /// AXI4+ATOP AW channel struct type for the slave ports.
  parameter type slv_aw_chan_t = logic,
  /// AXI4+ATOP AW channel struct type for the master ports.
  parameter type mst_aw_chan_t = logic,
  /// AXI4+ATOP W channel struct type for all ports.
  parameter type w_chan_t = logic,
  /// AXI4+ATOP B channel struct type for the slave ports.
  parameter type slv_b_chan_t = logic,
  /// AXI4+ATOP B channel struct type for the master ports.
  parameter type mst_b_chan_t = logic,
  /// AXI4+ATOP AR channel struct type for the slave ports.
  parameter type slv_ar_chan_t = logic,
  /// AXI4+ATOP AR channel struct type for the master ports.
  parameter type mst_ar_chan_t = logic,
  /// AXI4+ATOP R channel struct type for the slave ports.
  parameter type slv_r_chan_t = logic,
  /// AXI4+ATOP R channel struct type for the master ports.
  parameter type mst_r_chan_t = logic,
  /// AXI4+ATOP request struct type for the slave ports.
  parameter type slv_req_t = logic,
  /// AXI4+ATOP response struct type for the slave ports.
  parameter type slv_resp_t = logic,
  /// AXI4+ATOP request struct type for the master ports.
  parameter type mst_req_t = logic,
  /// AXI4+ATOP response struct type for the master ports.
  parameter type mst_resp_t = logic,
  /// Address rule type for the address decoders from `common_cells:addr_decode`.
  ///
  /// Example types are provided in `axi_pkg`.
  ///
  /// Required struct fields:
  ///
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   axi_addr_t   start_addr;
  ///   axi_addr_t   end_addr;
  /// } rule_t;
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// Dependent parameter, do **not** override!
  /// Width of the index specifying a master port.
  parameter int unsigned DefaultIdxWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not** override!
  /// Type of index for a default master port.
  parameter type default_idx_t = logic [DefaultIdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  /// Testmode enable, active high.
  input  logic test_i,
  /// AXI4+ATOP requests to the slave ports.
  input  slv_req_t  [NumSlvPorts-1:0] slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.
  output slv_resp_t [NumSlvPorts-1:0] slv_ports_resp_o,
  /// AXI4+ATOP requests of the master ports.
  output mst_req_t  [NumMstPorts-1:0] mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  mst_resp_t [NumMstPorts-1:0] mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t [NumAddrRules-1:0] addr_map_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  ///
  /// When not used, tie to `'0`.
  input  logic [NumSlvPorts-1:0] en_default_mst_port_i,
  /// For each slave port the default index where the transaction should be routed, if
  /// for this slave port the default index functionality is enabled by setting the
  /// bit `en_default_mst_port_i[slave_port_idx]` to `'1`.
  ///
  /// When not used, tie to `'0`.
  input  default_idx_t [NumSlvPorts-1:0] default_mst_port_i
);
  // AXI4+ATOP address type for the address decoders.
  typedef logic [AxiAddrWidth-1:0]            addr_t;
  // Separate type definition to account for the decoding error slave.
  typedef logic [$clog2(NumMstPorts + 1)-1:0] mst_port_idx_t;

  // Signals from the axi_demuxes, one index more for decode error.
  slv_req_t  [NumSlvPorts-1:0][NumMstPorts:0] slv_reqs;
  slv_resp_t [NumSlvPorts-1:0][NumMstPorts:0] slv_resps;

  // Signals into the axi_muxes, are of type slave as the multiplexer extends the ID.
  slv_req_t  [NumMstPorts-1:0][NumSlvPorts-1:0] mst_reqs;
  slv_resp_t [NumMstPorts-1:0][NumSlvPorts-1:0] mst_resps;

  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_slv_port_demux
    default_idx_t  dec_aw,        dec_ar;
    mst_port_idx_t slv_aw_select, slv_ar_select;
    logic          dec_aw_valid,  dec_aw_error;
    logic          dec_ar_valid,  dec_ar_error;

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .NoRules    ( NumAddrRules ),
      .addr_t     ( addr_t       ),
      .rule_t     ( rule_t       )
    ) i_axi_aw_decode (
      .addr_i           ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( dec_aw_valid               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .addr_t     ( addr_t       ),
      .NoRules    ( NumAddrRules ),
      .rule_t     ( rule_t       )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( dec_ar_valid               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    assign slv_aw_select = (dec_aw_error) ? mst_port_idx_t'(NumMstPorts) : mst_port_idx_t'(dec_aw);
    assign slv_ar_select = (dec_ar_error) ? mst_port_idx_t'(NumMstPorts) : mst_port_idx_t'(dec_ar);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Slave Port: %0d", i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Slave Port: %0d", i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Slave Port: %0d", i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Slave Port: %0d", i));
    `endif
    // pragma translate_on
    axi_demux #(
      .AxiIdWidth     ( AxiIdWidthSlvPorts  ),  // ID Width
      .aw_chan_t      ( slv_aw_chan_t       ),  // AW Channel Type
      .w_chan_t       ( w_chan_t            ),  //  W Channel Type
      .b_chan_t       ( slv_b_chan_t        ),  //  B Channel Type
      .ar_chan_t      ( slv_ar_chan_t       ),  // AR Channel Type
      .r_chan_t       ( slv_r_chan_t        ),  //  R Channel Type
      .req_t          ( slv_req_t           ),
      .resp_t         ( slv_resp_t          ),
      .NoMstPorts     ( NumMstPorts + 32'd1 ),
      .MaxTrans       ( MaxMstTrans         ),
      .AxiLookBits    ( AxiIdUsedSlvPorts   ),
      .FallThrough    ( FallThrough         ),
      .SpillAw        ( LatencyMode[9]      ),
      .SpillW         ( LatencyMode[8]      ),
      .SpillB         ( LatencyMode[7]      ),
      .SpillAr        ( LatencyMode[6]      ),
      .SpillR         ( LatencyMode[5]      )
    ) i_axi_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .slv_req_i       ( slv_ports_req_i[i]  ),
      .slv_aw_select_i ( slv_aw_select       ),
      .slv_ar_select_i ( slv_ar_select       ),
      .slv_resp_o      ( slv_ports_resp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]         ),
      .mst_resps_i     ( slv_resps[i]        )
    );

    axi_err_slv #(
      .AxiIdWidth  ( AxiIdWidthSlvPorts   ),
      .req_t       ( slv_req_t            ),
      .resp_t      ( slv_resp_t           ),
      .Resp        ( axi_pkg::RESP_DECERR ),
      .RespWidth   ( 32'd64               ),
      .RespData    ( 64'hCA11AB1EBADCAB1E ),
      .ATOPs       ( 1'b1                 ),
      .MaxTrans    ( 4                    )   // Transactions terminate at this slave, so minimize
                                              // resource consumption by accepting only a few
                                              // transactions at a time.
    ) i_axi_err_slv (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // slave port
      .slv_req_i  ( slv_reqs[i][NumMstPorts]   ),
      .slv_resp_o ( slv_resps[i][NumMstPorts]  )
    );
  end

  // cross all channels
  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; unsigned'(j) < NumMstPorts; j++) begin : gen_xbar_mst_cross
      axi_multicut #(
        .NoCuts    ( PipelineStages ),
        .aw_chan_t ( slv_aw_chan_t      ),
        .w_chan_t  ( w_chan_t           ),
        .b_chan_t  ( slv_b_chan_t       ),
        .ar_chan_t ( slv_ar_chan_t      ),
        .r_chan_t  ( slv_r_chan_t       ),
        .req_t     ( slv_req_t          ),
        .resp_t    ( slv_resp_t         )
      ) i_axi_multicut_xbar_pipeline (
        .clk_i,
        .rst_ni,
        .slv_req_i  ( slv_reqs[i][j]  ),
        .slv_resp_o ( slv_resps[i][j] ),
        .mst_req_o  ( mst_reqs[j][i]  ),
        .mst_resp_i ( mst_resps[j][i] )
      );
    end
  end

  for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_mst_port_mux
    axi_mux #(
      .SlvAxiIDWidth ( AxiIdWidthSlvPorts ), // ID width of the slave ports
      .slv_aw_chan_t ( slv_aw_chan_t      ), // AW Channel Type, slave ports
      .mst_aw_chan_t ( mst_aw_chan_t      ), // AW Channel Type, master port
      .w_chan_t      ( w_chan_t           ), //  W Channel Type, all ports
      .slv_b_chan_t  ( slv_b_chan_t       ), //  B Channel Type, slave ports
      .mst_b_chan_t  ( mst_b_chan_t       ), //  B Channel Type, master port
      .slv_ar_chan_t ( slv_ar_chan_t      ), // AR Channel Type, slave ports
      .mst_ar_chan_t ( mst_ar_chan_t      ), // AR Channel Type, master port
      .slv_r_chan_t  ( slv_r_chan_t       ), //  R Channel Type, slave ports
      .mst_r_chan_t  ( mst_r_chan_t       ), //  R Channel Type, master port
      .slv_req_t     ( slv_req_t          ),
      .slv_resp_t    ( slv_resp_t         ),
      .mst_req_t     ( mst_req_t          ),
      .mst_resp_t    ( mst_resp_t         ),
      .NoSlvPorts    ( NumSlvPorts        ), // Number of Masters for the module
      .MaxWTrans     ( MaxSlvTrans        ),
      .FallThrough   ( FallThrough        ),
      .SpillAw       ( LatencyMode[4]     ),
      .SpillW        ( LatencyMode[3]     ),
      .SpillB        ( LatencyMode[2]     ),
      .SpillAr       ( LatencyMode[1]     ),
      .SpillR        ( LatencyMode[0]     )
    ) i_axi_mux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Test Mode enable
      .slv_reqs_i  ( mst_reqs[i]         ),
      .slv_resps_o ( mst_resps[i]        ),
      .mst_req_o   ( mst_ports_req_o[i]  ),
      .mst_resp_i  ( mst_ports_resp_i[i] )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"
/// Interface wrapper for `axi_xbar`.
module axi_xbar_intf #(
  /// See `axi_xbar.NumSlvPorts`.
  parameter int unsigned NUM_SLV_PORTS = 32'd0,
  /// See `axi_xbar.NumMstPorts`.
  parameter int unsigned NUM_MST_PORTS = 32'd0,
  /// See `axi_xbar.MaxMstTrans`.
  parameter int unsigned MAX_MST_TRANS = 32'd8,
  /// See `axi_xbar.MaxSlvTrans`.
  parameter int unsigned MAX_SLV_TRANS = 32'd8,
  /// See `axi_xbar.FallThrough`.
  parameter bit FALL_THROUGH = 1'b0,
  /// See `axi_xbar.LatencyMode`.
  parameter axi_pkg::xbar_latency_e LATENCY_MODE = axi_pkg::CUT_ALL_AX,
  /// See `axi_xbar.PipelineStages`.
  parameter int unsigned PIPELINE_STAGES = 32'd0,
  /// See `axi_xbar.AxiIdWidthSlvPorts`.
  parameter int unsigned AXI_ID_WIDTH_SLV_PORTS = 32'd0,
  /// See `axi_xbar.AxiIdUsedSlvPorts`.
  parameter int unsigned AXI_ID_USED_SLV_PORTS = 32'd0,
  /// AXI4+ATOP address field width.
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  /// AXI4+ATOP data field width.
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  /// AXI4+ATOP user field width.
  parameter int unsigned AXI_USER_WIDTH = 32'd0,
  /// The number of address rules defined for routing of the transactions.
  /// Each master port can have multiple rules, should have however at least one.
  /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
  parameter int unsigned NUM_ADDR_RULES = 32'd0,
  /// See `axi_xbar.rule_t`.
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// Dependent parameter, do **not** override!
  /// Width of the index specifying a master port.
  parameter int unsigned DefaultIdxWidth = cf_math_pkg::idx_width(NUM_MST_PORTS),
  /// Dependent parameter, do **not** override!
  /// See `axi_xbar.default_idx_t`
  parameter type default_idx_t = logic [DefaultIdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  input  logic test_i,
  /// AXI4+ATOP slave port interfaces.
  AXI_BUS.Slave slv_ports [NUM_SLV_PORTS-1:0],
  /// AXI4+ATOP master port interfaces.
  AXI_BUS.Master mst_ports [NUM_MST_PORTS-1:0],
  /// Address map input. See `axi_xbar.addr_map_i`.
  input  rule_t [NUM_ADDR_RULES-1:0] addr_map_i,
  /// Default master port enable input. See `axi_xbar.en_default_mst_port_i`.
  input  logic  [NUM_SLV_PORTS-1:0] en_default_mst_port_i,
  /// Default master port indexes. See `axi_xbar.en_default_mst_port_i`.
  input  default_idx_t [NUM_SLV_PORTS-1:0] default_mst_port_i
);

  localparam int unsigned AXI_ID_WIDTH_MST_PORTS = AXI_ID_WIDTH_SLV_PORTS + $clog2(NUM_SLV_PORTS);

  typedef logic [AXI_ID_WIDTH_MST_PORTS-1:0] id_mst_t;
  typedef logic [AXI_ID_WIDTH_SLV_PORTS-1:0] id_slv_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]         addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]         data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]       strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]         user_t;

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, id_slv_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  mst_req_t  [NUM_MST_PORTS-1:0] mst_reqs;
  mst_resp_t [NUM_MST_PORTS-1:0] mst_resps;
  slv_req_t  [NUM_SLV_PORTS-1:0] slv_reqs;
  slv_resp_t [NUM_SLV_PORTS-1:0] slv_resps;

  for (genvar i = 0; unsigned'(i) < NUM_MST_PORTS; i++) begin : gen_assign_mst
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_resps[i], mst_ports[i])
  end

  for (genvar i = 0; unsigned'(i) < NUM_SLV_PORTS; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_xbar #(
    .NumSlvPorts        ( NUM_SLV_PORTS          ),
    .NumMstPorts        ( NUM_MST_PORTS          ),
    .MaxMstTrans        ( MAX_MST_TRANS          ),
    .MaxSlvTrans        ( MAX_SLV_TRANS          ),
    .FallThrough        ( FALL_THROUGH           ),
    .LatencyMode        ( LATENCY_MODE           ),
    .PipelineStages     ( PIPELINE_STAGES        ),
    .AxiIdWidthSlvPorts ( AXI_ID_WIDTH_SLV_PORTS ),
    .AxiIdUsedSlvPorts  ( AXI_ID_USED_SLV_PORTS  ),
    .AxiAddrWidth       ( AXI_ADDR_WIDTH         ),
    .AxiDataWidth       ( AXI_DATA_WIDTH         ),
    .NumAddrRules       ( NUM_ADDR_RULES         ),
    .slv_aw_chan_t      ( slv_aw_chan_t          ),
    .mst_aw_chan_t      ( mst_aw_chan_t          ),
    .w_chan_t           ( w_chan_t               ),
    .slv_b_chan_t       ( slv_b_chan_t           ),
    .mst_b_chan_t       ( mst_b_chan_t           ),
    .slv_ar_chan_t      ( slv_ar_chan_t          ),
    .mst_ar_chan_t      ( mst_ar_chan_t          ),
    .slv_r_chan_t       ( slv_r_chan_t           ),
    .mst_r_chan_t       ( mst_r_chan_t           ),
    .slv_req_t          ( slv_req_t              ),
    .slv_resp_t         ( slv_resp_t             ),
    .mst_req_t          ( mst_req_t              ),
    .mst_resp_t         ( mst_resp_t             ),
    .rule_t             ( rule_t                 )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i  (slv_reqs ),
    .slv_ports_resp_o (slv_resps),
    .mst_ports_req_o  (mst_reqs ),
    .mst_ports_resp_i (mst_resps),
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );
endmodule
