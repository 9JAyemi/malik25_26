module pio_latency_assertions (
    input  logic [1:0]  address,
    input  logic        clk,
    input  logic [15:0] in_port,
    input  logic        reset_n,
    input  logic [15:0] readdata
);

    // After reset was sampled low, readdata is zero on the next active clock.
    check_post_reset_readdata_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($past(reset_n) === 1'b0) |-> (readdata == 16'h0000)
    );

    // A prior read of address 0 returns the prior input, unless reset forced zero.
    check_addr0_read_matches_input_or_reset_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && ($past(address) === 2'b00)) |->
        ((readdata == $past(in_port)) || (readdata == 16'h0000))
    );

    // A prior read of address 1 returns zero.
    check_addr1_reads_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && ($past(address) === 2'b01)) |-> (readdata == 16'h0000)
    );

    // A prior read of address 2 returns zero.
    check_addr2_reads_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && ($past(address) === 2'b10)) |-> (readdata == 16'h0000)
    );

    // A prior read of address 3 returns zero.
    check_addr3_reads_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && ($past(address) === 2'b11)) |-> (readdata == 16'h0000)
    );

    // Address 0 with zero input returns zero on the following clock.
    check_addr0_zero_input_reads_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && ($past(address) === 2'b00) && ($past(in_port) === 16'h0000)) |->
        (readdata == 16'h0000)
    );

    // Any nonzero readdata must come from a prior read of address 0.
    check_nonzero_readdata_from_addr0: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(reset_n) === 1'b1) && (readdata != 16'h0000)) |->
        (($past(address) === 2'b00) && (readdata == $past(in_port)))
    );

endmodule