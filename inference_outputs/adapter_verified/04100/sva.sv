module gray_code_state_machine_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] out
);

// Reset drives the next state to 0.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (out == 4'd0)
    );

// State 0 maps to 0 on the next cycle.
    check_state_0_maps_to_0: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd0) |=> (out == 4'd0)
    );

// State 1 maps to 1 on the next cycle.
    check_state_1_maps_to_1: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd1) |=> (out == 4'd1)
    );

// State 2 maps to 3 on the next cycle.
    check_state_2_maps_to_3: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd2) |=> (out == 4'd3)
    );

// State 3 maps to 2 on the next cycle.
    check_state_3_maps_to_2: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd3) |=> (out == 4'd2)
    );

// State 4 maps to 6 on the next cycle.
    check_state_4_maps_to_6: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd4) |=> (out == 4'd6)
    );

// State 5 maps to 7 on the next cycle.
    check_state_5_maps_to_7: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd5) |=> (out == 4'd7)
    );

// State 6 maps to 5 on the next cycle.
    check_state_6_maps_to_5: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd6) |=> (out == 4'd5)
    );

// State 7 maps to 4 on the next cycle.
    check_state_7_maps_to_4: assert property (
        @(posedge clk) disable iff (rst) (out == 4'd7) |=> (out == 4'd4)
    );

endmodule
