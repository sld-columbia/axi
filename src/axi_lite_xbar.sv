// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "axi/typedef.svh"
/// axi_lite_xbar: Fully-connected AXI4-Lite crossbar.
/// See `doc/axi_lite_xbar.md` for the documentation,
/// including the definition of parameters and ports.
module axi_lite_xbar #(
  /// Number of slave ports of `axi_lite_xbar`.
  /// This many master modules are connected to it.
  parameter int unsigned NumSlvPorts = 32'd0,
  /// Number of master ports of `axi_lite_xbar`.
  /// This many slave modules are connected to it.
  parameter int unsigned NumMstPorts = 32'd0,
  /// The max number of open transactions each master connected to a slave port can have in flight.
  parameter int unsigned MaxMstTrans = 32'd8,
  /// The max number of open transactions each master port can generate to a slave module connected.
  parameter int unsigned MaxSlvTrans = 32'd8,
  /// The internal FIFOs are in fallthrough mode.
  parameter bit FallThrough = 1'b0,
  /// The Latency mode of the xbar. This determines if the channels on the ports have
  /// a spill register instantiated.
  /// Example configurations are provided with the enum `axi_pkg::xbar_latency_e`.
  parameter axi_pkg::xbar_latency_e LatencyMode = axi_pkg::CUT_ALL_AX,
  /// AXI4-Lite address field width.
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// AXI4-Lite data field width.
  parameter int unsigned AxiDataWidth = 32'd0,
  /// The number of address rules in the address map of the xbar.
  /// Each master port should have at least one rule specified.
  parameter int unsigned NumAddrRules = 32'd0,
  /// AXI4-Lite AW channel type.
  parameter type aw_chan_t = logic,
  /// AXI4-Lite W channel type.
  parameter type w_chan_t = logic,
  /// AXI4-Lite B channel type.
  parameter type b_chan_t = logic,
  /// AXI4-Lite AR channel type.
  parameter type ar_chan_t = logic,
  /// AXI4-Lite R channel type.
  parameter type r_chan_t = logic,
  /// AXI4-Lite request struct type.
  parameter type req_t = logic,
  /// AXI4-Lite response struct type.
  parameter type resp_t = logic,
  /// Address decoding rule.
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  /// Default master port index width.
  parameter int unsigned DefaultIdxWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  /// Index type of the default master port index.
  parameter type default_idx_t = logic[DefaultIdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Testmode enable, active high.
  input logic test_i,
  /// AXI4-Lite slave ports, requests.
  input req_t [NumSlvPorts-1:0] slv_ports_req_i,
  /// AXI4-Lite slave ports, responses.
  output resp_t [NumSlvPorts-1:0] slv_ports_resp_o,
  /// AXI4-Lite master ports, requests.
  output req_t [NumMstPorts-1:0] mst_ports_req_o,
  /// AXI4-Lite master ports, responses.
  input resp_t [NumMstPorts-1:0] mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input rule_t [NumAddrRules-1:0] addr_map_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  ///
  /// When not used, tie to `'0`.
  input logic [NumSlvPorts-1:0] en_default_mst_port_i,
  /// For each slave port the default index where the transaction should be routed, if
  /// for this slave port the default index functionality is enabled by setting the
  /// bit `en_default_mst_port_i[slave_port_idx]` to `'1`.
  ///
  /// When not used, tie to `'0`.
  input default_idx_t [NumSlvPorts-1:0] default_mst_port_i
);

  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  // to account for the decoding error slave
  typedef logic [$clog2(NumMstPorts + 1)-1:0] mst_port_idx_t;
  // full AXI typedef for the decode error slave, id_t and user_t are logic and will be
  // removed during logic optimization as they are stable
  `AXI_TYPEDEF_AW_CHAN_T(full_aw_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_W_CHAN_T(full_w_chan_t, data_t, strb_t, logic)
  `AXI_TYPEDEF_B_CHAN_T(full_b_chan_t, logic, logic)
  `AXI_TYPEDEF_AR_CHAN_T(full_ar_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_R_CHAN_T(full_r_chan_t, data_t, logic, logic)
  `AXI_TYPEDEF_REQ_T(full_req_t, full_aw_chan_t, full_w_chan_t, full_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(full_resp_t, full_b_chan_t, full_r_chan_t)

  // signals from the axi_lite_demuxes, one index more for decode error routing
  req_t  [NumSlvPorts-1:0][NumMstPorts:0] slv_reqs;
  resp_t [NumSlvPorts-1:0][NumMstPorts:0] slv_resps;

  // signals into the axi_lite_muxes, are of type slave as the multiplexer extends the ID
  req_t  [NumMstPorts-1:0][NumSlvPorts-1:0] mst_reqs;
  resp_t [NumMstPorts-1:0][NumSlvPorts-1:0] mst_resps;

  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_slv_port_demux
    default_idx_t  dec_aw,        dec_ar;
    mst_port_idx_t slv_aw_select, slv_ar_select;
    logic          dec_aw_error;
    logic          dec_ar_error;

    full_req_t  decerr_req;
    full_resp_t decerr_resp;

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .NoRules    ( NumAddrRules ),
      .addr_t     ( addr_t       ),
      .rule_t     ( rule_t       )
    ) i_axi_aw_decode (
      .addr_i           ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( /*not used*/               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .NoRules    ( NumAddrRules ),
      .addr_t     ( addr_t       ),
      .rule_t     ( rule_t       )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( /*not used*/               ),
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
    axi_lite_demux #(
      .aw_chan_t      ( aw_chan_t           ), // AW Channel Type
      .w_chan_t       ( w_chan_t            ), //  W Channel Type
      .b_chan_t       ( b_chan_t            ), //  B Channel Type
      .ar_chan_t      ( ar_chan_t           ), // AR Channel Type
      .r_chan_t       ( r_chan_t            ), //  R Channel Type
      .req_t          ( req_t               ),
      .resp_t         ( resp_t              ),
      .NoMstPorts     ( NumMstPorts + 32'd1 ),
      .MaxTrans       ( MaxMstTrans         ),
      .FallThrough    ( FallThrough         ),
      .SpillAw        ( LatencyMode[9]      ),
      .SpillW         ( LatencyMode[8]      ),
      .SpillB         ( LatencyMode[7]      ),
      .SpillAr        ( LatencyMode[6]      ),
      .SpillR         ( LatencyMode[5]      )
    ) i_axi_lite_demux (
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

    // connect the decode error module to the last index of the demux master port
    // typedef as the decode error slave uses full axi
    axi_lite_to_axi #(
      .AxiDataWidth ( AxiDataWidth  ),
      .req_lite_t   ( req_t         ),
      .resp_lite_t  ( resp_t        ),
      .req_t        ( full_req_t    ),
      .resp_t       ( full_resp_t   )
    ) i_dec_err_conv (
      .slv_req_lite_i  ( slv_reqs[i][NumMstPorts]  ),
      .slv_resp_lite_o ( slv_resps[i][NumMstPorts] ),
      .slv_aw_cache_i  ( 4'd0                      ),
      .slv_ar_cache_i  ( 4'd0                      ),
      .mst_req_o       ( decerr_req                ),
      .mst_resp_i      ( decerr_resp               )
    );

    axi_err_slv #(
      .AxiIdWidth  ( 32'd1                ), // ID width is one as defined as logic above
      .req_t       ( full_req_t           ), // AXI request struct
      .resp_t      ( full_resp_t          ), // AXI response struct
      .Resp        ( axi_pkg::RESP_DECERR ),
      .ATOPs       ( 1'b0                 ), // no ATOPs in AXI4-Lite
      .MaxTrans    ( 1                    )  // Transactions terminate at this slave, and AXI4-Lite
                                             // transactions have only a single beat.
    ) i_axi_err_slv (
      .clk_i,
      .rst_ni,
      .test_i,
      // slave port
      .slv_req_i  ( decerr_req  ),
      .slv_resp_o ( decerr_resp )
    );
  end

  // cross all channels
  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; unsigned'(j) < NumMstPorts; j++) begin : gen_xbar_mst_cross
      assign mst_reqs[j][i]  = slv_reqs[i][j];
      assign slv_resps[i][j] = mst_resps[j][i];
    end
  end

  for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_mst_port_mux
    axi_lite_mux #(
      .aw_chan_t   ( aw_chan_t      ), // AW Channel Type
      .w_chan_t    (  w_chan_t      ), //  W Channel Type
      .b_chan_t    (  b_chan_t      ), //  B Channel Type
      .ar_chan_t   ( ar_chan_t      ), // AR Channel Type
      .r_chan_t    (  r_chan_t      ), //  R Channel Type
      .req_t       ( req_t          ),
      .resp_t      ( resp_t         ),
      .NoSlvPorts  ( NumSlvPorts    ), // Number of Masters for the module
      .MaxTrans    ( MaxSlvTrans    ),
      .FallThrough ( FallThrough    ),
      .SpillAw     ( LatencyMode[4] ),
      .SpillW      ( LatencyMode[3] ),
      .SpillB      ( LatencyMode[2] ),
      .SpillAr     ( LatencyMode[1] ),
      .SpillR      ( LatencyMode[0] )
    ) i_axi_lite_mux (
      .clk_i,  // Clock
      .rst_ni, // Asynchronous reset active low
      .test_i, // Test Mode enable
      .slv_reqs_i  ( mst_reqs[i]         ),
      .slv_resps_o ( mst_resps[i]        ),
      .mst_req_o   ( mst_ports_req_o[i]  ),
      .mst_resp_i  ( mst_ports_resp_i[i] )
    );
  end
endmodule
