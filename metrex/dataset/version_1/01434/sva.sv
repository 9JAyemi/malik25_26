// SVA for dmem_mux3
// Concise end-to-end checks for decode, forward, and return paths, plus key coverage.
// Assumes a sampling clock/reset are available; bind with your clk/rst.

module dmem_mux3_sva #(parameter int ADDR_MUX_START = 28)
(
  input logic clk,
  input logic rst_n,

  // DUT ports
  input  logic [31:0] mem_addr_i,
  input  logic [31:0] mem_data_i,
  output logic [31:0] mem_data_o,
  input  logic [3:0]  mem_sel_i,
  input  logic        mem_we_i,
  input  logic        mem_stb_i,
  input  logic        mem_cyc_i,
  input  logic [2:0]  mem_cti_i,
  output logic        mem_ack_o,
  output logic        mem_stall_o,

  output logic [31:0] out0_addr_o,
  output logic [31:0] out0_data_o,
  input  logic [31:0] out0_data_i,
  output logic [3:0]  out0_sel_o,
  output logic        out0_we_o,
  output logic        out0_stb_o,
  output logic        out0_cyc_o,
  output logic [2:0]  out0_cti_o,
  input  logic        out0_ack_i,
  input  logic        out0_stall_i,

  output logic [31:0] out1_addr_o,
  output logic [31:0] out1_data_o,
  input  logic [31:0] out1_data_i,
  output logic [3:0]  out1_sel_o,
  output logic        out1_we_o,
  output logic        out1_stb_o,
  output logic        out1_cyc_o,
  output logic [2:0]  out1_cti_o,
  input  logic        out1_ack_i,
  input  logic        out1_stall_i,

  output logic [31:0] out2_addr_o,
  output logic [31:0] out2_data_o,
  input  logic [31:0] out2_data_i,
  output logic [3:0]  out2_sel_o,
  output logic        out2_we_o,
  output logic        out2_stb_o,
  output logic        out2_cyc_o,
  output logic [2:0]  out2_cti_o,
  input  logic        out2_ack_i,
  input  logic        out2_stall_i
);

  localparam int SEL_HI = ADDR_MUX_START+2-1;
  wire [1:0] sel = mem_addr_i[SEL_HI:ADDR_MUX_START];

  // Helper: no X on outputs when inputs and decode bits are known
  property p_no_x_propagation;
    (!$isunknown({sel,mem_data_i,mem_sel_i,mem_we_i,mem_stb_i,mem_cyc_i,mem_cti_i})) |->
    !$isunknown({
      out0_addr_o,out0_data_o,out0_sel_o,out0_we_o,out0_stb_o,out0_cyc_o,out0_cti_o,
      out1_addr_o,out1_data_o,out1_sel_o,out1_we_o,out1_stb_o,out1_cyc_o,out1_cti_o,
      out2_addr_o,out2_data_o,out2_sel_o,out2_we_o,out2_stb_o,out2_cyc_o,out2_cti_o,
      mem_data_o,mem_ack_o,mem_stall_o
    });
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_no_x_propagation);

  // Selected forward path must mirror mem_*; others forced to zero
  property p_sel0_forward;
    (sel==2'd0) |->
      (out0_addr_o==mem_addr_i && out0_data_o==mem_data_i && out0_sel_o==mem_sel_i &&
       out0_we_o==mem_we_i && out0_stb_o==mem_stb_i && out0_cyc_o==mem_cyc_i && out0_cti_o==mem_cti_i) &&
      (out1_addr_o==32'h0 && out1_data_o==32'h0 && out1_sel_o==4'h0 &&
       !out1_we_o && !out1_stb_o && !out1_cyc_o && out1_cti_o==3'h0) &&
      (out2_addr_o==32'h0 && out2_data_o==32'h0 && out2_sel_o==4'h0 &&
       !out2_we_o && !out2_stb_o && !out2_cyc_o && out2_cti_o==3'h0);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel0_forward);

  property p_sel1_forward;
    (sel==2'd1) |->
      (out1_addr_o==mem_addr_i && out1_data_o==mem_data_i && out1_sel_o==mem_sel_i &&
       out1_we_o==mem_we_i && out1_stb_o==mem_stb_i && out1_cyc_o==mem_cyc_i && out1_cti_o==mem_cti_i) &&
      (out0_addr_o==32'h0 && out0_data_o==32'h0 && out0_sel_o==4'h0 &&
       !out0_we_o && !out0_stb_o && !out0_cyc_o && out0_cti_o==3'h0) &&
      (out2_addr_o==32'h0 && out2_data_o==32'h0 && out2_sel_o==4'h0 &&
       !out2_we_o && !out2_stb_o && !out2_cyc_o && out2_cti_o==3'h0);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel1_forward);

  property p_sel2_forward;
    (sel==2'd2) |->
      (out2_addr_o==mem_addr_i && out2_data_o==mem_data_i && out2_sel_o==mem_sel_i &&
       out2_we_o==mem_we_i && out2_stb_o==mem_stb_i && out2_cyc_o==mem_cyc_i && out2_cti_o==mem_cti_i) &&
      (out0_addr_o==32'h0 && out0_data_o==32'h0 && out0_sel_o==4'h0 &&
       !out0_we_o && !out0_stb_o && !out0_cyc_o && out0_cti_o==3'h0) &&
      (out1_addr_o==32'h0 && out1_data_o==32'h0 && out1_sel_o==4'h0 &&
       !out1_we_o && !out1_stb_o && !out1_cyc_o && out1_cti_o==3'h0);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel2_forward);

  // Default decode (sel==3) forces all forward-path outputs to zero, return-path zeros
  property p_default_forward_return_zeros;
    (sel==2'd3) |->
      (out0_addr_o==32'h0 && out0_data_o==32'h0 && out0_sel_o==4'h0 &&
       !out0_we_o && !out0_stb_o && !out0_cyc_o && out0_cti_o==3'h0) &&
      (out1_addr_o==32'h0 && out1_data_o==32'h0 && out1_sel_o==4'h0 &&
       !out1_we_o && !out1_stb_o && !out1_cyc_o && out1_cti_o==3'h0) &&
      (out2_addr_o==32'h0 && out2_data_o==32'h0 && out2_sel_o==4'h0 &&
       !out2_we_o && !out2_stb_o && !out2_cyc_o && out2_cti_o==3'h0) &&
      (mem_data_o==32'h0 && !mem_ack_o && !mem_stall_o);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_default_forward_return_zeros);

  // Return path pass-through: mem_* mirrors selected slave inputs
  property p_sel0_return;
    (sel==2'd0) |->
      (mem_data_o==out0_data_i && mem_ack_o==out0_ack_i && mem_stall_o==out0_stall_i);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel0_return);

  property p_sel1_return;
    (sel==2'd1) |->
      (mem_data_o==out1_data_i && mem_ack_o==out1_ack_i && mem_stall_o==out1_stall_i);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel1_return);

  property p_sel2_return;
    (sel==2'd2) |->
      (mem_data_o==out2_data_i && mem_ack_o==out2_ack_i && mem_stall_o==out2_stall_i);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_sel2_return);

  // Mutual exclusivity and correctness of one-hot strobes/cyc/we when sel is valid
  function automatic bit [2:0] onehot_from_sel(input bit [1:0] s);
    return (s==2'd0) ? 3'b001 :
           (s==2'd1) ? 3'b010 :
           (s==2'd2) ? 3'b100 : 3'b000;
  endfunction

  property p_onehot_stb_when_valid_sel;
    (sel<=2 && mem_stb_i) |->
      ({out2_stb_o,out1_stb_o,out0_stb_o} == onehot_from_sel(sel));
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_onehot_stb_when_valid_sel);

  property p_onehot_cyc_when_valid_sel;
    (sel<=2 && mem_cyc_i) |->
      ({out2_cyc_o,out1_cyc_o,out0_cyc_o} == onehot_from_sel(sel));
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_onehot_cyc_when_valid_sel);

  property p_onehot_we_when_valid_sel;
    (sel<=2) |->
      ({out2_we_o,out1_we_o,out0_we_o} == (mem_we_i ? onehot_from_sel(sel) : 3'b000));
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_onehot_we_when_valid_sel);

  // If mem_stb_i or mem_cyc_i deasserted, no output strobe/cyc asserted regardless of sel
  property p_no_outputs_when_mem_idle;
    (!mem_stb_i && !mem_cyc_i) |->
      (!out0_stb_o && !out1_stb_o && !out2_stb_o &&
       !out0_cyc_o && !out1_cyc_o && !out2_cyc_o);
  endproperty
  assert property (@(posedge clk) disable iff (!rst_n) p_no_outputs_when_mem_idle);

  // Coverage: exercise each decode and default, with traffic
  cover property (@(posedge clk) disable iff (!rst_n) mem_stb_i && sel==2'd0);
  cover property (@(posedge clk) disable iff (!rst_n) mem_stb_i && sel==2'd1);
  cover property (@(posedge clk) disable iff (!rst_n) mem_stb_i && sel==2'd2);
  cover property (@(posedge clk) disable iff (!rst_n) mem_stb_i && sel==2'd3);

  // Coverage: return-path acknowledgments/stalls propagate for each target
  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd0 && out0_ack_i && mem_ack_o);
  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd1 && out1_ack_i && mem_ack_o);
  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd2 && out2_ack_i && mem_ack_o);

  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd0 && out0_stall_i && mem_stall_o);
  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd1 && out1_stall_i && mem_stall_o);
  cover property (@(posedge clk) disable iff (!rst_n) sel==2'd2 && out2_stall_i && mem_stall_o);

endmodule

// Bind example (adjust clk/rst as appropriate):
// bind dmem_mux3 dmem_mux3_sva #(.ADDR_MUX_START(ADDR_MUX_START)) dmem_mux3_sva_i (.* , .clk(tb_clk), .rst_n(tb_rst_n));