import axi_pkg::*;


module axi_intf_bind_slv
  #(
    parameter int AXI_ADDR_WIDTH = -1,
    parameter int AXI_DATA_WIDTH = -1,
    parameter int AXI_ID_WIDTH = -1,
    parameter int AXI_USER_WIDTH = -1,
    parameter int AXI_STRB_WIDTH = -1
    )
   (
    // Slave interface
    AXI_BUS.Slave in,
    // MST out
    output logic [AXI_ID_WIDTH-1:0]    mst_out_aw_id,
    output logic [AXI_ADDR_WIDTH-1:0]  mst_out_aw_addr,
    output logic [7:0] 		      mst_out_aw_len,
    output logic [2:0] 		      mst_out_aw_size,
    output 			      burst_t mst_out_aw_burst,
    output logic 		      mst_out_aw_lock,
    output 			      cache_t mst_out_aw_cache,
    output 			      prot_t mst_out_aw_prot,
    output 			      qos_t mst_out_aw_qos,
    output logic [5:0] 		      mst_out_aw_atop,
    output 			      region_t mst_out_aw_region,
    output logic [AXI_USER_WIDTH-1:0]  mst_out_aw_user,
    output logic 		      mst_out_aw_valid,

    output logic [AXI_DATA_WIDTH-1:0]  mst_out_w_data,
    output logic [AXI_STRB_WIDTH-1:0]  mst_out_w_strb,
    output logic 		      mst_out_w_last,
    output logic [AXI_USER_WIDTH-1:0]  mst_out_w_user,
    output logic 		      mst_out_w_valid,

    output logic 		      mst_out_b_ready,

    output logic [AXI_ID_WIDTH-1:0]    mst_out_ar_id,
    output logic [AXI_ADDR_WIDTH-1:0]  mst_out_ar_addr,
    output logic [7:0] 		      mst_out_ar_len,
    output logic [2:0] 		      mst_out_ar_size,
    output 			      burst_t mst_out_ar_burst,
    output logic 		      mst_out_ar_lock,
    output 			      cache_t mst_out_ar_cache,
    output 			      prot_t mst_out_ar_prot,
    output 			      qos_t mst_out_ar_qos,
    output 			      region_t mst_out_ar_region,
    output logic [AXI_USER_WIDTH-1:0]  mst_out_ar_user,
    output logic 		      mst_out_ar_valid,

    output logic 		      mst_out_r_ready,
    // MST in
    input logic 		      mst_in_aw_ready,

    input logic 		      mst_in_w_ready,

    input logic [AXI_ID_WIDTH-1:0]   mst_in_b_id,
    input 			      resp_t mst_in_b_resp,
    input logic [AXI_USER_WIDTH-1:0] mst_in_b_user,
    input logic 		      mst_in_b_valid,

    input logic 		      mst_in_ar_ready,

    input logic [AXI_ID_WIDTH-1:0]   mst_in_r_id,
    input logic [AXI_DATA_WIDTH-1:0] mst_in_r_data,
    input 			      resp_t mst_in_r_resp,
    input logic 		      mst_in_r_last,
    input logic [AXI_USER_WIDTH-1:0] mst_in_r_user,
    input logic 		      mst_in_r_valid
    );


   assign mst_out_aw_id = in.aw_id;
   assign mst_out_aw_addr = in.aw_addr;
   assign mst_out_aw_len = in.aw_len;
   assign mst_out_aw_size = in.aw_size;
   assign mst_out_aw_burst = in.aw_burst;
   assign mst_out_aw_lock = in.aw_lock;
   assign mst_out_aw_cache = in.aw_cache;
   assign mst_out_aw_prot = in.aw_prot;
   assign mst_out_aw_qos = in.aw_qos;
   assign mst_out_aw_region = in.aw_region;
   assign mst_out_aw_atop = in.aw_atop;
   assign mst_out_aw_user = in.aw_user;
   assign mst_out_aw_valid = in.aw_valid;
   assign in.aw_ready = mst_in_aw_ready;

   assign mst_out_w_data = in.w_data;
   assign mst_out_w_strb = in.w_strb;
   assign mst_out_w_last = in.w_last;
   assign mst_out_w_user = in.w_user;
   assign mst_out_w_valid = in.w_valid;
   assign in.w_ready = mst_in_w_ready;

   assign in.b_id = mst_in_b_id;
   assign in.b_resp = mst_in_b_resp;
   assign in.b_user = mst_in_b_user;
   assign in.b_valid = mst_in_b_valid;
   assign mst_out_b_ready = in.b_ready;

   assign mst_out_ar_id = in.ar_id;
   assign mst_out_ar_addr = in.ar_addr;
   assign mst_out_ar_len = in.ar_len;
   assign mst_out_ar_size = in.ar_size;
   assign mst_out_ar_burst = in.ar_burst;
   assign mst_out_ar_lock = in.ar_lock;
   assign mst_out_ar_cache = in.ar_cache;
   assign mst_out_ar_prot = in.ar_prot;
   assign mst_out_ar_qos = in.ar_qos;
   assign mst_out_ar_region = in.ar_region;
   assign mst_out_ar_user = in.ar_user;
   assign mst_out_ar_valid = in.ar_valid;
   assign in.ar_ready = mst_in_ar_ready;

   assign in.r_id = mst_in_r_id;
   assign in.r_data = mst_in_r_data;
   assign in.r_resp = mst_in_r_resp;
   assign in.r_last = mst_in_r_last;
   assign in.r_user = mst_in_r_user;
   assign in.r_valid = mst_in_r_valid;
   assign mst_out_r_ready = in.r_ready;

endmodule
