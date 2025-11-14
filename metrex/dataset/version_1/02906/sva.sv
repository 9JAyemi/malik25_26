// SVA for sky130_fd_sc_hd__a31oi: Y = ~(B1 | (A1 & A2 & A3))
module sky130_fd_sc_hd__a31oi_sva (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic A3,
  input logic B1
);
  default clocking cb @(*); endclocking

  // Functional equivalence when inputs are known
  property p_func;
    !$isunknown({A1,A2,A3,B1}) |-> (Y === ~(B1 | (A1 & A2 & A3)));
  endproperty
  assert property (p_func);

  // X-robust one-sided implications
  assert property (B1 === 1'b1 |-> Y === 1'b0);
  assert property ((A1===1'b1 && A2===1'b1 && A3===1'b1) |-> Y === 1'b0);
  assert property ((B1===1'b0 && (A1===1'b0 || A2===1'b0 || A3===1'b0)) |-> Y === 1'b1);
  assert property (Y === 1'b1 |-> (B1===1'b0 && (A1===1'b0 || A2===1'b0 || A3===1'b0)));

  // Output should not change without an input change
  assert property ($changed(Y) |-> $changed({A1,A2,A3,B1}));

  // Functional coverage of all 16 input combinations (and correct Y)
  genvar i;
  for (i = 0; i < 16; i++) begin : C
    localparam logic Bc  = i[3];
    localparam logic A3c = i[2];
    localparam logic A2c = i[1];
    localparam logic A1c = i[0];
    localparam logic Yexp = ~(Bc | (A3c & A2c & A1c));
    cover property ( ({B1,A3,A2,A1} === {Bc,A3c,A2c,A1c}) && (Y === Yexp) );
  end

  // Toggle coverage
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

bind sky130_fd_sc_hd__a31oi sky130_fd_sc_hd__a31oi_sva sva_i (
  .Y(Y), .A1(A1), .A2(A2), .A3(A3), .B1(B1)
);