module mux_2_to_1 (
  input in1,
  input in2,
  input select,
  output reg out
);

  always @ (select) begin
    if (select == 0) begin
      out <= in1;
    end else begin
      out <= in2;
    end
  end

endmodule
