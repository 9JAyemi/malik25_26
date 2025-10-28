module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output reg [3:0] sum,
    output reg cout
);

  reg [4:0] temp_sum;
  reg temp_cout;

  always @* begin
    temp_sum = a + b + cin;
    sum = temp_sum[3:0];
    temp_cout = (temp_sum > 4'b1111);
    cout = temp_cout;
  end

endmodule