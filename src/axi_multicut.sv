// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

import axi_pkg::*;


/// Multiple AXI4 cuts.
///
/// These can be used to relax timing pressure on very long AXI busses.
module axi_multicut #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  /// The ID width.
  parameter int ID_WIDTH = -1,
  // The user data width.
  parameter int USER_WIDTH = -1,
  // The number of cuts. Must be >= 0.
  parameter int NUM_CUTS = 0
)(
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
);


  localparam STRB_WIDTH = DATA_WIDTH / 8;

  typedef logic [ID_WIDTH-1:0]   id_t;
  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [STRB_WIDTH-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0] user_t;
  typedef logic [5:0] atop_t;

  typedef struct packed {
     id_t        aw_id;
     addr_t      aw_addr;
     logic [7:0] aw_len;
     logic [2:0] aw_size;
     burst_t     aw_burst;
     logic       aw_lock;
     cache_t     aw_cache;
     prot_t      aw_prot;
     qos_t       aw_qos;
     atop_t      aw_atop;
     region_t    aw_region;
     user_t      aw_user;
     logic       aw_valid;

     data_t      w_data;
     strb_t      w_strb;
     logic       w_last;
     user_t      w_user;
     logic       w_valid;

     logic       b_ready;

     id_t        ar_id;
     addr_t      ar_addr;
     logic [7:0] ar_len;
     logic [2:0] ar_size;
     burst_t     ar_burst;
     logic       ar_lock;
     cache_t     ar_cache;
     prot_t      ar_prot;
     qos_t       ar_qos;
     region_t    ar_region;
     user_t      ar_user;
     logic       ar_valid;

     logic       r_ready;
  } axi_mst_out_t;

   typedef struct packed {
      logic       aw_ready;

      logic       w_ready;

      id_t        b_id;
      resp_t      b_resp;
      user_t      b_user;
      logic       b_valid;

      logic       ar_ready;

      id_t        r_id;
      data_t      r_data;
      resp_t      r_resp;
      logic       r_last;
      user_t      r_user;
      logic       r_valid;
   } axi_mst_in_t;


  // Check the invariants.
  `ifndef SYNTHESIS
  initial begin
    assert(NUM_CUTS >= 0);
  end
  `endif

  // Handle the special case of no cuts.
  if (NUM_CUTS == 0) begin : g_cuts
    axi_join i_join (
      .in  ( in  ),
      .out ( out )
    );
  end

  // Handle the special case of one cut.
  else if (NUM_CUTS == 1) begin : g_cuts
    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_cut (
      .clk_i  ( clk_i  ),
      .rst_ni ( rst_ni ),
      .in     ( in     ),
      .out    ( out    )
    );
  end

  // Handle the cases of two or more cuts.
  else begin : g_cuts
    axi_mst_in_t s_cut_mst_in[NUM_CUTS-1:0];
    axi_mst_out_t s_cut_mst_out[NUM_CUTS-1:0];

    AXI_BUS #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH ),
      .AXI_ID_WIDTH   ( ID_WIDTH   ),
      .AXI_USER_WIDTH ( USER_WIDTH )
    ) first_if();

    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_first (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .in     ( in              ),
      .out    ( first_if.Master )
    );

    axi_intf_bind_slv #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH ),
      .AXI_ID_WIDTH   ( ID_WIDTH   ),
      .AXI_USER_WIDTH ( USER_WIDTH ),
      .AXI_STRB_WIDTH (STRB_WIDTH)
    ) i_first_bind (
      .in      ( first_if.Slave   ),

      .mst_out_aw_id (s_cut_mst_out[0].aw_id),
      .mst_out_aw_addr (s_cut_mst_out[0].aw_addr),
      .mst_out_aw_len (s_cut_mst_out[0].aw_len),
      .mst_out_aw_size (s_cut_mst_out[0].aw_size),
      .mst_out_aw_burst (s_cut_mst_out[0].aw_burst),
      .mst_out_aw_lock (s_cut_mst_out[0].aw_lock),
      .mst_out_aw_cache (s_cut_mst_out[0].aw_cache),
      .mst_out_aw_prot (s_cut_mst_out[0].aw_prot),
      .mst_out_aw_qos (s_cut_mst_out[0].aw_qos),
      .mst_out_aw_atop (s_cut_mst_out[0].aw_atop),
      .mst_out_aw_region (s_cut_mst_out[0].aw_region),
      .mst_out_aw_user (s_cut_mst_out[0].aw_user),
      .mst_out_aw_valid (s_cut_mst_out[0].aw_valid),
      .mst_out_w_data (s_cut_mst_out[0].w_data),
      .mst_out_w_strb (s_cut_mst_out[0].w_strb),
      .mst_out_w_last (s_cut_mst_out[0].w_last),
      .mst_out_w_user (s_cut_mst_out[0].w_user),
      .mst_out_w_valid (s_cut_mst_out[0].w_valid),
      .mst_out_b_ready (s_cut_mst_out[0].b_ready),
      .mst_out_ar_id (s_cut_mst_out[0].ar_id),
      .mst_out_ar_addr (s_cut_mst_out[0].ar_addr),
      .mst_out_ar_len (s_cut_mst_out[0].ar_len),
      .mst_out_ar_size (s_cut_mst_out[0].ar_size),
      .mst_out_ar_burst (s_cut_mst_out[0].ar_burst),
      .mst_out_ar_lock (s_cut_mst_out[0].ar_lock),
      .mst_out_ar_cache (s_cut_mst_out[0].ar_cache),
      .mst_out_ar_prot (s_cut_mst_out[0].ar_prot),
      .mst_out_ar_qos (s_cut_mst_out[0].ar_qos),
      .mst_out_ar_region (s_cut_mst_out[0].ar_region),
      .mst_out_ar_user (s_cut_mst_out[0].ar_user),
      .mst_out_ar_valid (s_cut_mst_out[0].ar_valid),
      .mst_out_r_ready (s_cut_mst_out[0].r_ready),

      .mst_in_aw_ready (s_cut_mst_in[0].aw_ready),
      .mst_in_w_ready (s_cut_mst_in[0].w_ready),
      .mst_in_b_id (s_cut_mst_in[0].b_id),
      .mst_in_b_resp (s_cut_mst_in[0].b_resp),
      .mst_in_b_user (s_cut_mst_in[0].b_user),
      .mst_in_b_valid (s_cut_mst_in[0].b_valid),
      .mst_in_ar_ready (s_cut_mst_in[0].ar_ready),
      .mst_in_r_id (s_cut_mst_in[0].r_id),
      .mst_in_r_data (s_cut_mst_in[0].r_data),
      .mst_in_r_resp (s_cut_mst_in[0].r_resp),
      .mst_in_r_last (s_cut_mst_in[0].r_last),
      .mst_in_r_user (s_cut_mst_in[0].r_user),
      .mst_in_r_valid (s_cut_mst_in[0].r_valid)
    );


    for (genvar i = 1; i < NUM_CUTS-1; i++) begin
      AXI_BUS #(
        .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( DATA_WIDTH ),
        .AXI_ID_WIDTH   ( ID_WIDTH   ),
        .AXI_USER_WIDTH ( USER_WIDTH )
      ) middle_if_1();

      AXI_BUS #(
        .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( DATA_WIDTH ),
        .AXI_ID_WIDTH   ( ID_WIDTH   ),
        .AXI_USER_WIDTH ( USER_WIDTH )
      ) middle_if_2();

      axi_intf_bind_mst #(
        .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( DATA_WIDTH ),
        .AXI_ID_WIDTH   ( ID_WIDTH   ),
        .AXI_USER_WIDTH ( USER_WIDTH ),
        .AXI_STRB_WIDTH ( STRB_WIDTH)
      ) i_middle_bind_1 (
      .mst_out_aw_id (s_cut_mst_out[i-1].aw_id),
      .mst_out_aw_addr (s_cut_mst_out[i-1].aw_addr),
      .mst_out_aw_len (s_cut_mst_out[i-1].aw_len),
      .mst_out_aw_size (s_cut_mst_out[i-1].aw_size),
      .mst_out_aw_burst (s_cut_mst_out[i-1].aw_burst),
      .mst_out_aw_lock (s_cut_mst_out[i-1].aw_lock),
      .mst_out_aw_cache (s_cut_mst_out[i-1].aw_cache),
      .mst_out_aw_prot (s_cut_mst_out[i-1].aw_prot),
      .mst_out_aw_qos (s_cut_mst_out[i-1].aw_qos),
      .mst_out_aw_atop (s_cut_mst_out[i-1].aw_atop),
      .mst_out_aw_region (s_cut_mst_out[i-1].aw_region),
      .mst_out_aw_user (s_cut_mst_out[i-1].aw_user),
      .mst_out_aw_valid (s_cut_mst_out[i-1].aw_valid),
      .mst_out_w_data (s_cut_mst_out[i-1].w_data),
      .mst_out_w_strb (s_cut_mst_out[i-1].w_strb),
      .mst_out_w_last (s_cut_mst_out[i-1].w_last),
      .mst_out_w_user (s_cut_mst_out[i-1].w_user),
      .mst_out_w_valid (s_cut_mst_out[i-1].w_valid),
      .mst_out_b_ready (s_cut_mst_out[i-1].b_ready),
      .mst_out_ar_id (s_cut_mst_out[i-1].ar_id),
      .mst_out_ar_addr (s_cut_mst_out[i-1].ar_addr),
      .mst_out_ar_len (s_cut_mst_out[i-1].ar_len),
      .mst_out_ar_size (s_cut_mst_out[i-1].ar_size),
      .mst_out_ar_burst (s_cut_mst_out[i-1].ar_burst),
      .mst_out_ar_lock (s_cut_mst_out[i-1].ar_lock),
      .mst_out_ar_cache (s_cut_mst_out[i-1].ar_cache),
      .mst_out_ar_prot (s_cut_mst_out[i-1].ar_prot),
      .mst_out_ar_qos (s_cut_mst_out[i-1].ar_qos),
      .mst_out_ar_region (s_cut_mst_out[i-1].ar_region),
      .mst_out_ar_user (s_cut_mst_out[i-1].ar_user),
      .mst_out_ar_valid (s_cut_mst_out[i-1].ar_valid),
      .mst_out_r_ready (s_cut_mst_out[i-1].r_ready),

      .mst_in_aw_ready (s_cut_mst_in[i-1].aw_ready),
      .mst_in_w_ready (s_cut_mst_in[i-1].w_ready),
      .mst_in_b_id (s_cut_mst_in[i-1].b_id),
      .mst_in_b_resp (s_cut_mst_in[i-1].b_resp),
      .mst_in_b_user (s_cut_mst_in[i-1].b_user),
      .mst_in_b_valid (s_cut_mst_in[i-1].b_valid),
      .mst_in_ar_ready (s_cut_mst_in[i-1].ar_ready),
      .mst_in_r_id (s_cut_mst_in[i-1].r_id),
      .mst_in_r_data (s_cut_mst_in[i-1].r_data),
      .mst_in_r_resp (s_cut_mst_in[i-1].r_resp),
      .mst_in_r_last (s_cut_mst_in[i-1].r_last),
      .mst_in_r_user (s_cut_mst_in[i-1].r_user),
      .mst_in_r_valid (s_cut_mst_in[i-1].r_valid),

        .out     ( middle_if_1.Master )
      );

      axi_cut #(
        .ADDR_WIDTH ( ADDR_WIDTH ),
        .DATA_WIDTH ( DATA_WIDTH ),
        .ID_WIDTH   ( ID_WIDTH   ),
        .USER_WIDTH ( USER_WIDTH )
      ) i_middle (
        .clk_i  ( clk_i              ),
        .rst_ni ( rst_ni             ),
        .in     ( middle_if_1.Slave  ),
        .out    ( middle_if_2.Master )
      );

      axi_intf_bind_slv #(
        .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( DATA_WIDTH ),
        .AXI_ID_WIDTH   ( ID_WIDTH   ),
        .AXI_USER_WIDTH ( USER_WIDTH ),
        .AXI_STRB_WIDTH ( STRB_WIDTH)
      ) i_middle_bind_2 (
      .in      ( middle_if_2.Slave ),

      .mst_out_aw_id (s_cut_mst_out[i].aw_id),
      .mst_out_aw_addr (s_cut_mst_out[i].aw_addr),
      .mst_out_aw_len (s_cut_mst_out[i].aw_len),
      .mst_out_aw_size (s_cut_mst_out[i].aw_size),
      .mst_out_aw_burst (s_cut_mst_out[i].aw_burst),
      .mst_out_aw_lock (s_cut_mst_out[i].aw_lock),
      .mst_out_aw_cache (s_cut_mst_out[i].aw_cache),
      .mst_out_aw_prot (s_cut_mst_out[i].aw_prot),
      .mst_out_aw_qos (s_cut_mst_out[i].aw_qos),
      .mst_out_aw_atop (s_cut_mst_out[i].aw_atop),
      .mst_out_aw_region (s_cut_mst_out[i].aw_region),
      .mst_out_aw_user (s_cut_mst_out[i].aw_user),
      .mst_out_aw_valid (s_cut_mst_out[i].aw_valid),
      .mst_out_w_data (s_cut_mst_out[i].w_data),
      .mst_out_w_strb (s_cut_mst_out[i].w_strb),
      .mst_out_w_last (s_cut_mst_out[i].w_last),
      .mst_out_w_user (s_cut_mst_out[i].w_user),
      .mst_out_w_valid (s_cut_mst_out[i].w_valid),
      .mst_out_b_ready (s_cut_mst_out[i].b_ready),
      .mst_out_ar_id (s_cut_mst_out[i].ar_id),
      .mst_out_ar_addr (s_cut_mst_out[i].ar_addr),
      .mst_out_ar_len (s_cut_mst_out[i].ar_len),
      .mst_out_ar_size (s_cut_mst_out[i].ar_size),
      .mst_out_ar_burst (s_cut_mst_out[i].ar_burst),
      .mst_out_ar_lock (s_cut_mst_out[i].ar_lock),
      .mst_out_ar_cache (s_cut_mst_out[i].ar_cache),
      .mst_out_ar_prot (s_cut_mst_out[i].ar_prot),
      .mst_out_ar_qos (s_cut_mst_out[i].ar_qos),
      .mst_out_ar_region (s_cut_mst_out[i].ar_region),
      .mst_out_ar_user (s_cut_mst_out[i].ar_user),
      .mst_out_ar_valid (s_cut_mst_out[i].ar_valid),
      .mst_out_r_ready (s_cut_mst_out[i].r_ready),

      .mst_in_aw_ready (s_cut_mst_in[i].aw_ready),
      .mst_in_w_ready (s_cut_mst_in[i].w_ready),
      .mst_in_b_id (s_cut_mst_in[i].b_id),
      .mst_in_b_resp (s_cut_mst_in[i].b_resp),
      .mst_in_b_user (s_cut_mst_in[i].b_user),
      .mst_in_b_valid (s_cut_mst_in[i].b_valid),
      .mst_in_ar_ready (s_cut_mst_in[i].ar_ready),
      .mst_in_r_id (s_cut_mst_in[i].r_id),
      .mst_in_r_data (s_cut_mst_in[i].r_data),
      .mst_in_r_resp (s_cut_mst_in[i].r_resp),
      .mst_in_r_last (s_cut_mst_in[i].r_last),
      .mst_in_r_user (s_cut_mst_in[i].r_user),
      .mst_in_r_valid (s_cut_mst_in[i].r_valid)

    );

    end

    AXI_BUS #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH ),
      .AXI_ID_WIDTH   ( ID_WIDTH   ),
      .AXI_USER_WIDTH ( USER_WIDTH )
    ) last_if();

    axi_intf_bind_mst #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH ),
      .AXI_ID_WIDTH   ( ID_WIDTH   ),
      .AXI_USER_WIDTH ( USER_WIDTH ),
      .AXI_STRB_WIDTH ( STRB_WIDTH)
    ) i_last_bind (

      .mst_out_aw_id (s_cut_mst_out[NUM_CUTS-2].aw_id),
      .mst_out_aw_addr (s_cut_mst_out[NUM_CUTS-2].aw_addr),
      .mst_out_aw_len (s_cut_mst_out[NUM_CUTS-2].aw_len),
      .mst_out_aw_size (s_cut_mst_out[NUM_CUTS-2].aw_size),
      .mst_out_aw_burst (s_cut_mst_out[NUM_CUTS-2].aw_burst),
      .mst_out_aw_lock (s_cut_mst_out[NUM_CUTS-2].aw_lock),
      .mst_out_aw_cache (s_cut_mst_out[NUM_CUTS-2].aw_cache),
      .mst_out_aw_prot (s_cut_mst_out[NUM_CUTS-2].aw_prot),
      .mst_out_aw_qos (s_cut_mst_out[NUM_CUTS-2].aw_qos),
      .mst_out_aw_atop (s_cut_mst_out[NUM_CUTS-2].aw_atop),
      .mst_out_aw_region (s_cut_mst_out[NUM_CUTS-2].aw_region),
      .mst_out_aw_user (s_cut_mst_out[NUM_CUTS-2].aw_user),
      .mst_out_aw_valid (s_cut_mst_out[NUM_CUTS-2].aw_valid),
      .mst_out_w_data (s_cut_mst_out[NUM_CUTS-2].w_data),
      .mst_out_w_strb (s_cut_mst_out[NUM_CUTS-2].w_strb),
      .mst_out_w_last (s_cut_mst_out[NUM_CUTS-2].w_last),
      .mst_out_w_user (s_cut_mst_out[NUM_CUTS-2].w_user),
      .mst_out_w_valid (s_cut_mst_out[NUM_CUTS-2].w_valid),
      .mst_out_b_ready (s_cut_mst_out[NUM_CUTS-2].b_ready),
      .mst_out_ar_id (s_cut_mst_out[NUM_CUTS-2].ar_id),
      .mst_out_ar_addr (s_cut_mst_out[NUM_CUTS-2].ar_addr),
      .mst_out_ar_len (s_cut_mst_out[NUM_CUTS-2].ar_len),
      .mst_out_ar_size (s_cut_mst_out[NUM_CUTS-2].ar_size),
      .mst_out_ar_burst (s_cut_mst_out[NUM_CUTS-2].ar_burst),
      .mst_out_ar_lock (s_cut_mst_out[NUM_CUTS-2].ar_lock),
      .mst_out_ar_cache (s_cut_mst_out[NUM_CUTS-2].ar_cache),
      .mst_out_ar_prot (s_cut_mst_out[NUM_CUTS-2].ar_prot),
      .mst_out_ar_qos (s_cut_mst_out[NUM_CUTS-2].ar_qos),
      .mst_out_ar_region (s_cut_mst_out[NUM_CUTS-2].ar_region),
      .mst_out_ar_user (s_cut_mst_out[NUM_CUTS-2].ar_user),
      .mst_out_ar_valid (s_cut_mst_out[NUM_CUTS-2].ar_valid),
      .mst_out_r_ready (s_cut_mst_out[NUM_CUTS-2].r_ready),

      .mst_in_aw_ready (s_cut_mst_in[NUM_CUTS-2].aw_ready),
      .mst_in_w_ready (s_cut_mst_in[NUM_CUTS-2].w_ready),
      .mst_in_b_id (s_cut_mst_in[NUM_CUTS-2].b_id),
      .mst_in_b_resp (s_cut_mst_in[NUM_CUTS-2].b_resp),
      .mst_in_b_user (s_cut_mst_in[NUM_CUTS-2].b_user),
      .mst_in_b_valid (s_cut_mst_in[NUM_CUTS-2].b_valid),
      .mst_in_ar_ready (s_cut_mst_in[NUM_CUTS-2].ar_ready),
      .mst_in_r_id (s_cut_mst_in[NUM_CUTS-2].r_id),
      .mst_in_r_data (s_cut_mst_in[NUM_CUTS-2].r_data),
      .mst_in_r_resp (s_cut_mst_in[NUM_CUTS-2].r_resp),
      .mst_in_r_last (s_cut_mst_in[NUM_CUTS-2].r_last),
      .mst_in_r_user (s_cut_mst_in[NUM_CUTS-2].r_user),
      .mst_in_r_valid (s_cut_mst_in[NUM_CUTS-2].r_valid),

      .out     ( last_if.Master )
      );

    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_last (
      .clk_i  ( clk_i                   ),
      .rst_ni ( rst_ni                  ),
      .in     ( last_if.Slave           ),
      .out    ( out                     )
    );
  end

endmodule
