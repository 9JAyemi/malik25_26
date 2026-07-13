module usb_type_c_orientation(
  input wire cc1,
  input wire cc2,
  output reg orientation
);

  always @(*) begin
    if (cc1 && !cc2) begin
      orientation = 1'b1; // Orientation A
    end else if (!cc1 && cc2) begin
      orientation = 1'b0; // Orientation B
    end else begin
      orientation = 1'bx; // Undefined
    end
  end

endmodule