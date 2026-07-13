module button_pio_sva (
    input logic [1:0] address,
    input logic       clk,
    input logic [3:0] in_port,
    input logic       reset_n,
    input logic [3:0] readdata
);

    // Active-low reset clears the registered read data.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 4'b0000)
    );

    // Address 0 loads the next read data value from the sampled input port.
    check_address_zero_returns_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |=> (readdata == $past(in_port))
    );

    // Any nonzero address loads zero into the read data register.
    check_nonzero_address_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |=> (readdata == 4'b0000)
    );

endmodule