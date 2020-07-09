import axi_pkg::*;


module axi_intf_bind_mst
  #(
    parameter int AXI_ADDR_WIDTH = -1,
    parameter int AXI_DATA_WIDTH = -1,
    parameter int AXI_ID_WIDTH = -1,
    parameter int AXI_USER_WIDTH = -1,
    parameter int AXI_STRB_WIDTH = -1
    )
   (
    // MST out
    input logic [AXI_ID_WIDTH-1:0]    mst_out_aw_id,
    input logic [AXI_ADDR_WIDTH-1:0]  mst_out_aw_addr,
    input logic [7:0]                 mst_out_aw_len,
    input logic [2:0]                 mst_out_aw_size,
    input                             burst_t mst_out_aw_burst,
    input logic                       mst_out_aw_lock,
    input                             cache_t mst_out_aw_cache,
    input                             prot_t mst_out_aw_prot,
    input                             qos_t mst_out_aw_qos,
    input logic [5:0]                 mst_out_aw_atop,
    input                             region_t mst_out_aw_region,
    input logic [AXI_USER_WIDTH-1:0]  mst_out_aw_user,
    input logic                       mst_out_aw_valid,
    input logic [AXI_DATA_WIDTH-1:0]  mst_out_w_data,
    input logic [AXI_STRB_WIDTH-1:0]  mst_out_w_strb,
    input logic                       mst_out_w_last,
    input logic [AXI_USER_WIDTH-1:0]  mst_out_w_user,
    input logic                       mst_out_w_valid,
    input logic                       mst_out_b_ready,
    input logic [AXI_ID_WIDTH-1:0]    mst_out_ar_id,
    input logic [AXI_ADDR_WIDTH-1:0]  mst_out_ar_addr,
    input logic [7:0]                 mst_out_ar_len,
    input logic [2:0]                 mst_out_ar_size,
    input                             burst_t mst_out_ar_burst,
    input logic                       mst_out_ar_lock,
    input                             cache_t mst_out_ar_cache,
    input                             prot_t mst_out_ar_prot,
    input                             qos_t mst_out_ar_qos,
    input                             region_t mst_out_ar_region,
    input logic [AXI_USER_WIDTH-1:0]  mst_out_ar_user,
    input logic                       mst_out_ar_valid,
    input logic                       mst_out_r_ready,
    // MST in
    output logic                      mst_in_aw_ready,
    output logic                      mst_in_w_ready,
    output logic [AXI_ID_WIDTH-1:0]   mst_in_b_id,
    output                            resp_t mst_in_b_resp,
    output logic [AXI_USER_WIDTH-1:0] mst_in_b_user,
    output logic                      mst_in_b_valid,
    output logic                      mst_in_ar_ready,
    output logic [AXI_ID_WIDTH-1:0]   mst_in_r_id,
    output logic [AXI_DATA_WIDTH-1:0] mst_in_r_data,
    output                            resp_t mst_in_r_resp,
    output logic                      mst_in_r_last,
    output logic [AXI_USER_WIDTH-1:0] mst_in_r_user,
    output logic                      mst_in_r_valid,
    // MST interface
    AXI_BUS.Master out
    );


   assign out.aw_id = mst_out_aw_id;
   assign out.aw_addr = mst_out_aw_addr;
   assign out.aw_len = mst_out_aw_len;
   assign out.aw_size = mst_out_aw_size;
   assign out.aw_burst = mst_out_aw_burst;
   assign out.aw_lock = mst_out_aw_lock;
   assign out.aw_cache = mst_out_aw_cache;
   assign out.aw_prot = mst_out_aw_prot;
   assign out.aw_qos = mst_out_aw_qos;
   assign out.aw_region = mst_out_aw_region;
   assign out.aw_atop = mst_out_aw_atop;
   assign out.aw_user = mst_out_aw_user;
   assign out.aw_valid = mst_out_aw_valid;
   assign mst_in_aw_ready = out.aw_ready;

   assign out.w_data = mst_out_w_data;
   assign out.w_strb = mst_out_w_strb;
   assign out.w_last = mst_out_w_last;
   assign out.w_user = mst_out_w_user;
   assign out.w_valid = mst_out_w_valid;
   assign mst_in_w_ready = out.w_ready;

   assign mst_in_b_id = out.b_id;
   assign mst_in_b_resp = out.b_resp;
   assign mst_in_b_user = out.b_user;
   assign mst_in_b_valid = out.b_valid;
   assign out.b_ready = mst_out_b_ready;

   assign out.ar_id = mst_out_ar_id;
   assign out.ar_addr = mst_out_ar_addr;
   assign out.ar_len = mst_out_ar_len;
   assign out.ar_size = mst_out_ar_size;
   assign out.ar_burst = mst_out_ar_burst;
   assign out.ar_lock = mst_out_ar_lock;
   assign out.ar_cache = mst_out_ar_cache;
   assign out.ar_prot = mst_out_ar_prot;
   assign out.ar_qos = mst_out_ar_qos;
   assign out.ar_region = mst_out_ar_region;
   assign out.ar_user = mst_out_ar_user;
   assign out.ar_valid = mst_out_ar_valid;
   assign mst_in_ar_ready = out.ar_ready;

   assign mst_in_r_id = out.r_id;
   assign mst_in_r_data = out.r_data;
   assign mst_in_r_resp = out.r_resp;
   assign mst_in_r_last = out.r_last;
   assign mst_in_r_user = out.r_user;
   assign mst_in_r_valid = out.r_valid;
   assign out.r_ready = mst_out_r_ready;

endmodule
