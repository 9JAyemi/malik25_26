module dna_sequencer_sva #(
    parameter [95:0] SIM_DNA_VALUE = 96'h000000000000000000000000
) (
    input logic DOUT,
    input logic CLK,
    input logic DIN,
    input logic READ,
    input logic SHIFT
);

    localparam integer MAX_DNA_BITS  = 96;
    localparam integer SHIFT_PIPELINE = MAX_DNA_BITS + 1;

    genvar i;

    // READ loads SIM_DNA_VALUE and drives its LSB on DOUT.
    check_read_loads_lsb: assert property (
        @(posedge CLK) READ |=> (DOUT == SIM_DNA_VALUE[0])
    );

    // READ takes priority over SHIFT when both are high.
    check_read_priority_over_shift: assert property (
        @(posedge CLK) (READ && SHIFT) |=> (DOUT == SIM_DNA_VALUE[0])
    );

    // With neither READ nor SHIFT, DOUT holds its value.
    check_idle_holds_dout: assert property (
        @(posedge CLK) (!READ && !SHIFT) |=> $stable(DOUT)
    );

    generate
        for (i = 0; i < MAX_DNA_BITS; i = i + 1) begin : gen_shifted_sim_bit_checks
            localparam integer SHIFT_COUNT = i + 1;
            // After READ and SHIFT_COUNT SHIFT cycles, DOUT presents SIM_DNA_VALUE[SHIFT_COUNT-1].
            check_shifted_sim_bit: assert property (
                @(posedge CLK) READ ##1 ((!READ && SHIFT)[*SHIFT_COUNT]) |=> (DOUT == SIM_DNA_VALUE[i])
            );
        end
    endgenerate

    // After 97 consecutive SHIFT cycles without READ, DOUT is DIN delayed through the shift path.
    check_shift_pipeline_delay: assert property (
        @(posedge CLK) ((!READ && SHIFT)[*SHIFT_PIPELINE]) |=> (DOUT == $past(DIN, SHIFT_PIPELINE))
    );

endmodule