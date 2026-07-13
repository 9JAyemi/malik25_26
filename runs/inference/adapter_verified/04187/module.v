module dff_en(input D, C, E, output Q);
  reg Q;

  always @(posedge C) begin
    if (E) begin
      Q <= D;
    end
  end

endmodule