module sensor_interface (
  input clk,
  input [7:0] temp_data,
  input [7:0] pressure_data,
  input [7:0] humidity_data,
  output temp_ready,
  output pressure_ready,
  output humidity_ready,
  output reg [7:0] temp_out,
  output reg [7:0] pressure_out,
  output reg [7:0] humidity_out
);

parameter clk_freq = 100000000; // 100 MHz clock
parameter sample_freq = 100; // sample at 100 Hz

reg [31:0] sample_counter = 0;
reg temp_ready_reg = 0;
reg pressure_ready_reg = 0;
reg humidity_ready_reg = 0;

always @(posedge clk) begin
  // increment sample counter
  sample_counter <= sample_counter + 1;

  // check if it's time to sample the sensors
  if (sample_counter == clk_freq / sample_freq) begin
    // reset sample counter
    sample_counter <= 0;

    // sample sensor data
    temp_out <= temp_data;
    pressure_out <= pressure_data;
    humidity_out <= humidity_data;

    // set ready signals high for one clock cycle
    temp_ready_reg <= 1;
    pressure_ready_reg <= 1;
    humidity_ready_reg <= 1;
  end else begin
    // set ready signals low
    temp_ready_reg <= 0;
    pressure_ready_reg <= 0;
    humidity_ready_reg <= 0;
  end
end

// assign ready signals to output ports
assign temp_ready = temp_ready_reg;
assign pressure_ready = pressure_ready_reg;
assign humidity_ready = humidity_ready_reg;

endmodule