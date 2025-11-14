module top_module (
  input clk,
  input reset,
  input [7:0] serial_input,
  output reg [9:0] accumulated_output
);

  reg [7:0] serial_data;
  reg [2:0] cycle_count;
  wire average_valid;

  accu accumulator(
    .clk(clk),
    .rst_n(!reset),
    .data_in(serial_data),
    .valid_a(average_valid),
    .ready_b(1'b1),
    .ready_a(),
    .valid_b(),
    .data_out(accumulated_output)
  );

  always @(posedge clk) begin
    if (reset) begin
      serial_data <= 8'h00;
      cycle_count <= 3'b0;
    end else begin
      serial_data <= serial_input;
      cycle_count <= cycle_count + 1;
    end
  end

  assign average_valid = (cycle_count == 3'b111);

endmodule

module accu(
  input clk,
  input rst_n,
  input [7:0] data_in,
  input valid_a,
  input ready_b,
  output reg ready_a,
  output reg valid_b,
  output reg [9:0] data_out
);

  reg [9:0] accumulator;
  reg [2:0] cycle_count;
  wire average_valid;

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      accumulator <= 10'h000;
      cycle_count <= 3'b0;
      ready_a <= 1'b0;
      valid_b <= 1'b0;
    end else begin
      if (valid_a && ready_b) begin
        accumulator <= accumulator + data_in;
        cycle_count <= cycle_count + 1;
        if (cycle_count == 3'b111) begin
          data_out <= accumulator / 6;
          accumulator <= 10'h000;
          cycle_count <= 3'b0;
          ready_a <= 1'b1;
          valid_b <= 1'b1;
        end else begin
          ready_a <= 1'b0;
          valid_b <= 1'b0;
        end
      end else begin
        ready_a <= 1'b0;
        valid_b <= 1'b0;
      end
    end
  end

endmodule