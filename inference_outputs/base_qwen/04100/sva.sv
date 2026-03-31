```systemverilog
module gray_code_state_machine_sva (
    input logic clk,
    input logic rst,
    output logic [n-1:0] out
);

parameter n = 4; // number of output signals

reg [n-1:0] state;
reg [n-1:0] gray_code;

always @ (posedge clk) begin
  if (rst) begin
    state <= 0;
  end else begin
    state <= gray_code;
  end
end

always @* begin
  case (state)
    0: gray_code = 0;
    1: gray_code = 1;
    2: gray_code = 3;
    3: gray_code = 2;
    4: gray_code = 6;
    5: gray_code = 7;
    6: gray_code = 5;
    7: gray_code = 4;
    default: gray_code = 0;
  endcase
end

assign out = gray_code;

///// State machine behavior /////
// State transitions are driven by the clock edge.
state_transition: assert property (
    @(posedge clk) disable iff (!rst) state !== gray_code
);

// Gray code is updated on each clock edge.
gray_code_update: assert property (
    @(posedge clk) disable iff (!rst) out == gray_code
);

// State 0 is the initial state.
initial_state: assert property (
    @(posedge clk) disable iff (!rst) state == 0
);

// State transitions are within the defined range.
state_range: assert property (
    @(posedge clk) disable iff (!rst) (state >= 0 && state <= 7)
);

// Gray code values are within the defined range.
gray_code_range: assert property (
    @(posedge clk) disable iff (!rst) (out >= 0 && out <= 7)
);

// State transitions are deterministic.
deterministic_transition: assert property (
    @(posedge clk) disable iff (!rst) $onehot(state) |-> $onehot(gray_code)
);

// Gray code values are deterministic.
deterministic_gray_code: assert property (
    @(posedge clk) disable iff (!rst) $onehot(out) |-> $onehot(gray_code)
);

endmodule
```