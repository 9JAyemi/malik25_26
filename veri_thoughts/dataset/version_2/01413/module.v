module logic_operations(a, b, g_out, p_out);
  input a, b;
  output g_out, p_out;

  // XOR operation
  XOR2_X1 U1 (.A(a), .B(b), .Z(p_out));

  // AND operation
  AND2_X1 U2 (.A1(a), .A2(b), .Z(g_out));
endmodule

module XOR2_X1(
    input A,
    input B,
    output Z
);

assign Z = A ^ B;  // XOR operation

endmodule

module AND2_X1(
    input A1,
    input A2,
    output Z
);

assign Z = A1 & A2;  // AND operation

endmodule
