
module parity_check (
  input [7:0] data_in,
  input control,
  output reg parity
);

  integer i;
  reg [7:0] data_temp;
  reg parity_temp;

  always @ (data_in, control) begin
    if (control == 0) begin
      parity <= 0;
    end else begin
      data_temp <= data_in;
      parity_temp <= 0;
      for (i = 0; i < 8; i = i + 1) begin
        parity_temp <= parity_temp ^ data_temp[i];
      end
      parity <= parity_temp;
    end
  end

endmodule