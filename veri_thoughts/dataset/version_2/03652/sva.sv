module shift_register_sva (
    input logic       clk,
    input logic [3:0] data_in,
    input logic [3:0] data_out,
    input logic [3:0] q
);

    // data_out must mirror the internal register q.
    check_data_out_matches_q: assert property (
        @(posedge clk) data_out == q
    );

    // q must shift left and load the previous data_in[0] each cycle.
    check_q_shift_update: assert property (
        @(posedge clk) 1'b1 |=> q == {$past(q[2:0]), $past(data_in[0])}
    );

    // q[0] must load the previous data_in[0].
    check_q_bit0_loads_data_in0: assert property (
        @(posedge clk) 1'b1 |=> q[0] == $past(data_in[0])
    );

    // q[1] must receive the previous q[0].
    check_q_bit1_shifts_from_bit0: assert property (
        @(posedge clk) 1'b1 |=> q[1] == $past(q[0])
    );

    // q[2] must receive the previous q[1].
    check_q_bit2_shifts_from_bit1: assert property (
        @(posedge clk) 1'b1 |=> q[2] == $past(q[1])
    );

    // q[3] must receive the previous q[2].
    check_q_bit3_shifts_from_bit2: assert property (
        @(posedge clk) 1'b1 |=> q[3] == $past(q[2])
    );

    // data_out must show the shifted register value each cycle.
    check_data_out_shift_update: assert property (
        @(posedge clk) 1'b1 |=> data_out == {$past(data_out[2:0]), $past(data_in[0])}
    );

    // data_out[0] must load the previous data_in[0].
    check_data_out_bit0_loads_data_in0: assert property (
        @(posedge clk) 1'b1 |=> data_out[0] == $past(data_in[0])
    );

    // data_out[1] must receive the previous data_out[0].
    check_data_out_bit1_shifts_from_bit0: assert property (
        @(posedge clk) 1'b1 |=> data_out[1] == $past(data_out[0])
    );

    // data_out[2] must receive the previous data_out[1].
    check_data_out_bit2_shifts_from_bit1: assert property (
        @(posedge clk) 1'b1 |=> data_out[2] == $past(data_out[1])
    );

    // data_out[3] must receive the previous data_out[2].
    check_data_out_bit3_shifts_from_bit2: assert property (
        @(posedge clk) 1'b1 |=> data_out[3] == $past(data_out[2])
    );

endmodule