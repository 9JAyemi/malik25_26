module TCMP_sva (
    input logic clk,
    input logic rst,
    input logic a,
    input logic ld,
    input logic s,
    input logic z
);

    // Reset holds both registers low.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |-> ((s == 1'b0) && (z == 1'b0))
    );

    // Load clears both registers on the next clock.
    check_load_clears_state: assert property (
        @(posedge clk) disable iff (rst)
        ld |=> ((s == 1'b0) && (z == 1'b0))
    );

    // With z clear and a low, the state stays clear.
    check_clear_state_zero_input: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (z == 1'b0) && (a == 1'b0)) |=> ((z == 1'b0) && (s == 1'b0))
    );

    // With z clear and a high, both registers set.
    check_clear_state_one_input: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (z == 1'b0) && (a == 1'b1)) |=> ((z == 1'b1) && (s == 1'b1))
    );

    // With z set and a low, z stays set and s goes high.
    check_set_state_zero_input: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (z == 1'b1) && (a == 1'b0)) |=> ((z == 1'b1) && (s == 1'b1))
    );

    // With z set and a high, z stays set and s goes low.
    check_set_state_one_input: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (z == 1'b1) && (a == 1'b1)) |=> ((z == 1'b1) && (s == 1'b0))
    );

    // Once z is set, it stays set until reset or load.
    check_z_sticky_without_load: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (z == 1'b1)) |=> (z == 1'b1)
    );

endmodule