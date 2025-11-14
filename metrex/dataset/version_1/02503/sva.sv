// SVA for BIU. Bind this module to the DUT: bind BIU BIU_sva biu_sva_i(.*);

module BIU_sva(
  input logic clk, rst,

  input  logic      wb_d_ack_i, wb_d_err_i, wb_d_rty_i,
  input  logic [31:0] wb_d_dat_i,
  input  logic      wb_c_ack_i, wb_c_err_i, wb_c_rty_i,
  input  logic [7:0]  wb_c_dat_i,
  input  logic [15:0] txt_dina,
  input  logic [31:0] MIO_data4bus_i,

  input  logic      Cpu_mem_w_i, Cpu_req_i,
  input  logic [31:0] Cpu_data2bus_i, Cpu_addr_bus_i,

  input  logic      wb_d_cyc_o, wb_d_stb_o, wb_d_we_o,
  input  logic [3:0]  wb_d_sel_o,
  input  logic [31:0] wb_d_adr_o, wb_d_dat_o,

  input  logic      wb_c_stb_o, wb_c_we_o,
  input  logic [31:0] wb_c_adr_o,
  input  logic [7:0]  wb_c_dat_o,

  input  logic      MIO_mem_w_o,
  input  logic [31:0] MIO_data2bus_o, MIO_addr_bus_o,

  input  logic [31:0] Cpu_data4bus_o,
  input  logic        Cpu_ready_o,

  input  logic        txt_ena, txt_wea,
  input  logic [12:0] txt_addra,
  input  logic [15:0] txt_douta,

  input  logic [31:0] gpu_status
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Address decodes
wire sel_wbd = (Cpu_addr_bus_i[31:28] == 4'h3);
wire sel_txt = (Cpu_addr_bus_i[31:28] == 4'hb) && ~Cpu_addr_bus_i[27];
wire sel_gpu = (Cpu_addr_bus_i[31:28] == 4'hb) &&  Cpu_addr_bus_i[27];
wire sel_wbc = (Cpu_addr_bus_i[31:28] == 4'hc);
wire sel_def = ~(sel_wbd | sel_txt | sel_gpu | sel_wbc);

// Constant pass-through mappings
assert property (MIO_data2bus_o == Cpu_data2bus_i);
assert property (wb_d_dat_o    == Cpu_data2bus_i);
assert property (wb_c_dat_o    == Cpu_data2bus_i);
assert property (txt_douta     == Cpu_data2bus_i);

assert property (MIO_addr_bus_o == Cpu_addr_bus_i);
assert property (wb_d_adr_o     == Cpu_addr_bus_i);
assert property (wb_c_adr_o     == Cpu_addr_bus_i);
assert property (txt_addra      == Cpu_addr_bus_i);

assert property (wb_d_sel_o == 4'hF);

// Region behavior: WB-D (0x3...)
assert property (sel_wbd |-> wb_d_we_o == Cpu_mem_w_i);
assert property (sel_wbd |-> wb_d_cyc_o == Cpu_req_i && wb_d_stb_o == Cpu_req_i);
assert property (sel_wbd |-> Cpu_data4bus_o == wb_d_dat_i && Cpu_ready_o == wb_d_ack_i);
// No other targets active when WB-D selected
assert property (sel_wbd |-> !wb_c_stb_o && !txt_ena && !MIO_mem_w_o);

// Region behavior: TXT (0xb..., bit27=0)
assert property (sel_txt |-> txt_wea == Cpu_mem_w_i && txt_ena == Cpu_req_i);
assert property (sel_txt |-> Cpu_data4bus_o == txt_dina && Cpu_ready_o == 1'b1);
// No other targets active when TXT selected
assert property (sel_txt |-> !wb_d_stb_o && !wb_d_cyc_o && !wb_c_stb_o && !MIO_mem_w_o);

// Region behavior: GPU (0xb..., bit27=1)
assert property (sel_gpu |-> Cpu_data4bus_o == gpu_status && Cpu_ready_o == 1'b1);
// No other targets active when GPU selected
assert property (sel_gpu |-> !wb_d_stb_o && !wb_d_cyc_o && !wb_c_stb_o && !txt_ena && !MIO_mem_w_o);

// Region behavior: WB-C (0xc...)
assert property (sel_wbc |-> wb_c_we_o == Cpu_mem_w_i && wb_c_stb_o == Cpu_req_i);
assert property (sel_wbc |-> Cpu_data4bus_o == wb_c_dat_i && Cpu_ready_o == wb_c_ack_i);
// No other targets active when WB-C selected
assert property (sel_wbc |-> !wb_d_stb_o && !wb_d_cyc_o && !txt_ena && !MIO_mem_w_o);

// Region behavior: DEFAULT (others)
assert property (sel_def |-> MIO_mem_w_o == Cpu_mem_w_i);
assert property (sel_def |-> Cpu_data4bus_o == MIO_data4bus_i && Cpu_ready_o == MIO_ready_i);
assert property (sel_def |-> !wb_d_stb_o && !wb_d_cyc_o && !wb_c_stb_o && !txt_ena);

// One-hot-ish enable implications
assert property (wb_d_stb_o |-> sel_wbd && wb_d_stb_o == Cpu_req_i);
assert property (wb_d_cyc_o |-> sel_wbd && wb_d_cyc_o == Cpu_req_i);
assert property (wb_d_we_o  |-> sel_wbd && wb_d_we_o  == Cpu_mem_w_i);

assert property (wb_c_stb_o |-> sel_wbc && wb_c_stb_o == Cpu_req_i);
assert property (wb_c_we_o  |-> sel_wbc && wb_c_we_o  == Cpu_mem_w_i);

assert property (txt_ena    |-> sel_txt && txt_ena == Cpu_req_i);
assert property (txt_wea    |-> sel_txt && txt_wea == Cpu_mem_w_i);

assert property (MIO_mem_w_o |-> sel_def);

// Ready only when ack for WB paths
assert property (sel_wbd && !wb_d_ack_i |-> !Cpu_ready_o);
assert property (sel_wbc && !wb_c_ack_i |-> !Cpu_ready_o);

// Ignore err/rty: ready must not assert without ack
assert property (sel_wbd && (wb_d_err_i || wb_d_rty_i) && !wb_d_ack_i |-> !Cpu_ready_o);
assert property (sel_wbc && (wb_c_err_i || wb_c_rty_i) && !wb_c_ack_i |-> !Cpu_ready_o);

// gpu_status reset and write side-effect
assert property (rst |-> gpu_status == 32'h0);
property gpu_wr_p;
  sel_gpu && Cpu_req_i && Cpu_mem_w_i;
endproperty
assert property (gpu_wr_p |=> gpu_status == $past(Cpu_data2bus_i));
assert property (!gpu_wr_p |=> gpu_status == $past(gpu_status));

// Coverage: exercise each region (read and write where applicable)
cover property (sel_wbd && Cpu_req_i && !Cpu_mem_w_i && wb_d_ack_i);
cover property (sel_wbd && Cpu_req_i &&  Cpu_mem_w_i && wb_d_ack_i);

cover property (sel_wbc && Cpu_req_i && !Cpu_mem_w_i && wb_c_ack_i);
cover property (sel_wbc && Cpu_req_i &&  Cpu_mem_w_i && wb_c_ack_i);

cover property (sel_txt && Cpu_req_i && !Cpu_mem_w_i);
cover property (sel_txt && Cpu_req_i &&  Cpu_mem_w_i);

cover property (sel_gpu && Cpu_req_i &&  Cpu_mem_w_i); // write GPU status
cover property (sel_gpu && !Cpu_mem_w_i);              // read GPU status

cover property (sel_def && !Cpu_mem_w_i && Cpu_ready_o);
cover property (sel_def &&  Cpu_mem_w_i && Cpu_ready_o);

// Sequence: write GPU then read back next cycle
cover property ( (sel_gpu && Cpu_req_i && Cpu_mem_w_i, 1'b1) ##1 (sel_gpu && !Cpu_mem_w_i) );

endmodule