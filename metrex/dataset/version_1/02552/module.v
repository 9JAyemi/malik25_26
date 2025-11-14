module dff_en #(parameter width_p = 1, harden_p = 1, strength_p = 1)
  (input clock_i,
   input [width_p-1:0] data_i,
   input en_i,
   output reg [width_p-1:0] data_o);

  reg [width_p-1:0] data_r;

  always @(posedge clock_i) begin
    if (en_i) begin
      data_r <= data_i;
    end
  end

  always @* begin
    data_o <= data_r;
  end

endmodule