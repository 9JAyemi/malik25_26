module temperature_sensor (
  input [9:0] analog_in,
  output reg [3:0] temp_range
);

  always @* begin
    case(analog_in)
      0: temp_range = 4'b0000; // below 0 degrees Celsius
      1: temp_range = 4'b0001; // below 0 degrees Celsius
      2: temp_range = 4'b0001; // below 0 degrees Celsius
      3: temp_range = 4'b0001; // below 0 degrees Celsius
      4: temp_range = 4'b0001; // below 0 degrees Celsius
      5: temp_range = 4'b0001; // below 0 degrees Celsius
      6: temp_range = 4'b0001; // below 0 degrees Celsius
      7: temp_range = 4'b0001; // below 0 degrees Celsius
      8: temp_range = 4'b0001; // below 0 degrees Celsius
      9: temp_range = 4'b0001; // below 0 degrees Celsius
      10: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      11: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      12: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      13: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      14: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      15: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      16: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      17: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      18: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      19: temp_range = 4'b0010; // 0 to 10 degrees Celsius
      20: temp_range = 4'b0011; // 10 to 20 degrees Celsius
      21: temp_range = 4'b0011; // 10 to 20 degrees Celsius
      22: temp_range = 4'b0011; // 10 to 20 degrees Celsius
      23: temp_range = 4'b0011; // 10 to 20 degrees Celsius
      24: temp_range = 4'b0011; // 10 to 20 degrees Celsius
      25: temp_range = 4'b0100; // above 20 degrees Celsius
      26: temp_range = 4'b0100; // above 20 degrees Celsius
      27: temp_range = 4'b0100; // above 20 degrees Celsius
      28: temp_range = 4'b0100; // above 20 degrees Celsius
      29: temp_range = 4'b0100; // above 20 degrees Celsius
      30: temp_range = 4'b0100; // above 20 degrees Celsius
      31: temp_range = 4'b0100; // above 20 degrees Celsius
      32: temp_range = 4'b0100; // above 20 degrees Celsius
      33: temp_range = 4'b0100; // above 20 degrees Celsius
      34: temp_range = 4'b0100; // above 20 degrees Celsius
      default: temp_range = 4'b0000; // below 0 degrees Celsius (default case)
    endcase
  end

endmodule