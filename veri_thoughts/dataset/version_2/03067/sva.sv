module spw_light_connecting_sva (
    input logic [1:0]  address,
    input logic        clk,
    input logic        in_port,
    input logic        reset_n,
    input logic [31:0] readdata
);

    // Active-low reset drives readdata low.
    check_reset_low_drives_zero: assert property (
        @(posedge clk) (!reset_n) |-> (readdata == 32'h00000000)
    );

    // A sampled reset low keeps readdata cleared into the next cycle.
    check_reset_low_keeps_zero_next_cycle: assert property (
        @(posedge clk) (!reset_n) |=> (readdata == 32'h00000000)
    );

    // Address 00 with a low input writes zero on the next clock.
    check_addr00_low_writes_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((address === 2'b00) && (in_port === 1'b0)) |=> (readdata == 32'h00000000)
    );

    // Address 01 writes zero on the next clock.
    check_addr01_writes_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address === 2'b01) |=> (readdata == 32'h00000000)
    );

    // Address 10 writes zero on the next clock.
    check_addr10_writes_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address === 2'b10) |=> (readdata == 32'h00000000)
    );

    // Address 11 writes zero on the next clock.
    check_addr11_writes_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address === 2'b11) |=> (readdata == 32'h00000000)
    );

    // Every enabled write keeps the upper 31 bits cleared.
    check_next_readdata_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata[31:1] == 31'b0)
    );

endmodule