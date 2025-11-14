
module constant_voltage_driver (
  input clk,
  input rst,
  input ctrl,
  output reg vout
);

parameter voltage_level = 1800; // desired voltage level of the output signal in mV
parameter rise_time = 10; // time required for the output signal to rise to the desired voltage level in ns
parameter fall_time = 20; // time required for the output signal to fall from the desired voltage level in ns

reg [31:0] rise_counter;
reg [31:0] fall_counter;

always @(posedge clk) begin
  if (rst) begin
    vout <= 0;
    rise_counter <= 0;
    fall_counter <= 0;
  end
  else begin
    if (ctrl) begin
      if (rise_counter < rise_time) begin
        rise_counter <= rise_counter + 1;
        vout <= (rise_counter * voltage_level) / rise_time;
      end
      else begin
        vout <= voltage_level;
      end
      fall_counter <= 0;
    end
    else begin
      if (fall_counter < fall_time) begin
        fall_counter <= fall_counter + 1;
        vout <= voltage_level - ((fall_counter * voltage_level) / fall_time);
      end
      else begin
        vout <= 0;
      end
      rise_counter <= 0;
    end
  end
end

endmodule