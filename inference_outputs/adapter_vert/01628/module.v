module debouncer (
  input clk,
  input in,
  output reg out
);

parameter clk_freq = 100000; // clock frequency in Hz
parameter debounce_time = 10; // debounce time in ms

reg [1:0] state;
reg [31:0] debounce_count;

localparam STABLE = 2'b00;
localparam UNSTABLE = 2'b01;
localparam DEBOUNCE = 2'b10;

always @(posedge clk) begin
  case(state)
    STABLE: begin
      if(in != out) begin
        state <= UNSTABLE;
        debounce_count <= debounce_time * clk_freq / 1000;
      end
    end
    UNSTABLE: begin
      if(debounce_count == 0) begin
        state <= DEBOUNCE;
        out <= in;
      end else begin
        debounce_count <= debounce_count - 1;
      end
    end
    DEBOUNCE: begin
      if(in != out) begin
        state <= UNSTABLE;
        debounce_count <= debounce_time * clk_freq / 1000;
      end else begin
        state <= STABLE;
      end
    end
  endcase
end

endmodule