
module mux
  #(
    parameter INIT_VAL = 8'hB8
  )
  (
    input ctrl,
    input D0,
    input D1,
    output S
  );

  assign S = ctrl ? D1 : D0;

  // Verilog-XL specific way of implementing this MUX
  wire mux_out = INIT_VAL[ctrl ? 0 : 4];

endmodule