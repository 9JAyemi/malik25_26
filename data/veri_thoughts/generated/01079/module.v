
module sffsrce_fdre (
  output Q,
  input C,
  input CE,
  input D,
  input R,
  input SET,
  input RESET
);

  reg Q_int;

  always @(posedge C) begin
    if (CE) begin
      if (SET)
        Q_int <= 1'b1;
      else if (RESET)
        Q_int <= 1'b0;
      else if (R)
        Q_int <= D;
    end
  end

  assign Q = Q_int;

endmodule

module FFAR (
  output Q,
  input C,
  input CE,
  input D,
  input R
);

  wire S;
  wire Rn;
  wire Dn;

  assign S = 1'b0;
  assign Rn = R;
  assign Dn = D;

  sffsrce_fdre sffsrce (
    .Q(Q),
    .C(C),
    .CE(CE),
    .D(Dn),
    .R(Rn),
    .SET(S),
    .RESET(S)
  );

endmodule
