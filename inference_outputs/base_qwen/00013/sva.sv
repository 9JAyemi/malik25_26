module mux_4to1_using_2to1_sva (
  input logic CLK,
  input logic [7:0] data0,
  input logic [7:0] data1,
  input logic [7:0] data2,
  input logic [7:0] data3,
  input logic [1:0] sel,
  output logic [7:0] out
);

  // Mux0 selects between data0 and data1 based on sel[0]
  mux0_select: assert property (
    @(posedge CLK) $rose(sel[0]) |-> (out == (sel[0] ? data1 : data0))
  );

  // Mux1 selects between data2 and data3 based on sel[0]
  mux1_select: assert property (
    @(posedge CLK) $rose(sel[0]) |-> (mux0_out == (sel[0] ? data1 : data0))
  );

  // Final mux selects between the outputs of Mux0 and Mux1 based on sel[1]
  final_mux_select: assert property (
    @(posedge CLK) $rose(sel[1]) |-> (out == (sel[1] ? mux1_out : mux0_out))
  );

endmodule