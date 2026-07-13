module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] q
);

    property p_load_captures_data;
        logic [3:0] sampled_data;
        @(posedge clk)
            (load, sampled_data = data)
            |=> (q == sampled_data);
    endproperty

    property p_shift_when_not_load;
        logic [3:0] sampled_q;
        @(posedge clk)
            (!load, sampled_q = q)
            |=> (q == {sampled_q[2:0], 1'b0});
    endproperty

    property p_shift_bit3_from_bit2;
        logic [3:0] sampled_q;
        @(posedge clk)
            (!load, sampled_q = q)
            |=> (q[3] == sampled_q[2]);
    endproperty

    property p_shift_bit2_from_bit1;
        logic [3:0] sampled_q;
        @(posedge clk)
            (!load, sampled_q = q)
            |=> (q[2] == sampled_q[1]);
    endproperty

    property p_shift_bit1_from_bit0;
        logic [3:0] sampled_q;
        @(posedge clk)
            (!load, sampled_q = q)
            |=> (q[1] == sampled_q[0]);
    endproperty

    // Loading copies data into q on the next clock.
    check_load_captures_data: assert property (p_load_captures_data);

    // When load is low, q shifts left and inserts 0.
    check_shift_when_not_load: assert property (p_shift_when_not_load);

    // A shift moves old q[2] into q[3].
    check_shift_bit3_from_bit2: assert property (p_shift_bit3_from_bit2);

    // A shift moves old q[1] into q[2].
    check_shift_bit2_from_bit1: assert property (p_shift_bit2_from_bit1);

    // A shift moves old q[0] into q[1].
    check_shift_bit1_from_bit0: assert property (p_shift_bit1_from_bit0);

    // A shift always inserts 0 into q[0].
    check_shift_inserts_zero: assert property (
        @(posedge clk) !load |=> (q[0] == 1'b0)
    );

    // Four consecutive shifts clear the register.
    check_four_shifts_clear_register: assert property (
        @(posedge clk) ((!load)[*4]) |=> (q == 4'b0000)
    );

    // Zero remains zero while shifting without a load.
    check_zero_holds_without_load: assert property (
        @(posedge clk) (!load && (q == 4'b0000)) |=> (q == 4'b0000)
    );

endmodule