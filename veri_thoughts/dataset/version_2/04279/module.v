
module tri_buf (in, out, en);
  input in;
  input en;
  output wire out;
  supply1 VCC;
  assign out = en ? in : VCC;
endmodule