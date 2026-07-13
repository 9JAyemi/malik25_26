module udp_mux_4to1_sva (
  input logic CLK,
  input logic [3:0] out,
  input logic [3:0] in0, in1, in2, in3,
  input logic [1:0] sel
);
  // Mux selection logic must be driven by sel
  mux_selection: assert property (
    @(posedge CLK) disable iff (!CLK) $rose(out) |-> (sel == 2'b00 || sel == 2'b01 || sel == 2'b10 || sel == 2'b11)
  );

  // Output must be one of the inputs based on the selection
  mux_output: assert property (
    @(posedge CLK) disable iff (!CLK) $rose(out) |-> 
      (sel == 2'b00 && out == in0[0]) || 
      (sel == 2'b01 && out == in1[0]) || 
      (sel == 2'b10 && out == in2[0]) || 
      (sel == 2'b11 && out == in3[0])
  );

  // Sequential logic in mux_2to1 module
  // No need for additional assertions as the logic is purely combinational
endmodule