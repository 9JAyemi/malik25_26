module shift_register_sva (
    input  logic        clk,
    input  logic [3:0]  data_in,
    input  logic        shift_in,
    input  logic        load,
    input  logic [3:0]  data_out,
    input  logic [3:0]  shift_reg
);

    ///// Combinational pass-through /////
    // data_out continuously mirrors internal shift_reg.
    check_dataout_mirrors_shiftreg: assert property (
        @(posedge clk) data_out == shift_reg
    );

    ///// Next-state behavior /////
    // Next-cycle data_out equals load ? data_in : {data_out[2:0], shift_in}.
    check_next_state_equation: assert property (
        @(posedge clk) 1'b1 |=> (data_out == ($sampled(load) ? $sampled(data_in) : { $sampled(data_out[2:0]), $sampled(shift_in) }))
    );

    ///// Load behavior /////
    // When load is asserted, next-cycle data_out equals sampled data_in.
    load_captures_data_in_next_cycle: assert property (
        @(posedge clk) load |=> (data_out == $sampled(data_in))
    );

    ///// Shift behavior (bit-wise) /////
    // When shifting, next-cycle MSB comes from prior bit[2].
    shift_moves_msb_from_bit2: assert property (
        @(posedge clk) !load |=> (data_out[3] == $sampled(data_out[2]))
    );
    // When shifting, next-cycle bit[2] comes from prior bit[1].
    shift_moves_bit2_from_bit1: assert property (
        @(posedge clk) !load |=> (data_out[2] == $sampled(data_out[1]))
    );
    // When shifting, next-cycle bit[1] comes from prior bit[0].
    shift_moves_bit1_from_bit0: assert property (
        @(posedge clk) !load |=> (data_out[1] == $sampled(data_out[0]))
    );
    // When shifting, next-cycle LSB comes from sampled shift_in.
    shift_in_captures_into_lsb: assert property (
        @(posedge clk) !load |=> (data_out[0] == $sampled(shift_in))
    );

    ///// Multi-cycle behavior /////
    // Two consecutive shifts produce a two-bit left shift with two sampled shift_in bits.
    two_consecutive_shifts_chain: assert property (
        @(posedge clk) ($past(!load,2) && $past(!load,1)) |-> (data_out == { $past(data_out[1:0],2), $past(shift_in,2), $past(shift_in,1) })
    );
    // Two consecutive loads result in data_out taking the most recent sampled data_in.
    two_consecutive_loads_last_sample_kept: assert property (
        @(posedge clk) ($past(load,2) && $past(load,1)) |-> (data_out == $past(data_in,1))
    );

endmodule