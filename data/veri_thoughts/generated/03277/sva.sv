module nios_dut_pio_0_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        in_port,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic        irq,
    input logic [31:0] readdata
);

    // Reset drives the registered output and interrupt low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> ((readdata == 32'h00000000) && (irq == 1'b0))
    );

    // Readdata is always zero-extended from a 1-bit source.
    check_readdata_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (readdata[31:1] == 31'b0)
    );

    // Address 0 is sampled into readdata on the next clock.
    check_address0_reads_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |=> (readdata == {31'b0, $past(in_port)})
    );

    // Unmapped addresses return zero on the next clock.
    check_unmapped_addresses_read_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((address != 2'b00) && (address != 2'b10)) |=> (readdata == 32'h00000000)
    );

    // IRQ can only be high when the input bit is high.
    check_irq_requires_input_high: assert property (
        @(posedge clk) disable iff (!reset_n)
        irq |-> in_port
    );

    // Writing a 0 to address 2 clears the interrupt mask effect.
    check_write_zero_clears_irq: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b10) && (writedata[0] == 1'b0)) |=> (irq == 1'b0)
    );

    // Writing a 1 to address 2 makes IRQ follow the input bit.
    check_write_one_sets_irq_behavior: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b10) && (writedata[0] == 1'b1)) |=> (irq == in_port)
    );

    // Reading address 2 with input high returns the prior cycle's IRQ state.
    check_address2_read_matches_prev_irq_when_input_high: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((address == 2'b10) && in_port) |=> (readdata == {31'b0, $past(irq)})
    );

    // A write of 0 is readable at address 2 after the next address-2 sample.
    check_write_zero_readback_at_address2: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((chipselect && !write_n && (address == 2'b10) && (writedata[0] == 1'b0)) ##1 (address == 2'b10))
        |=> (readdata == 32'h00000000)
    );

    // A write of 1 is readable at address 2 after the next address-2 sample.
    check_write_one_readback_at_address2: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((chipselect && !write_n && (address == 2'b10) && (writedata[0] == 1'b1)) ##1 (address == 2'b10))
        |=> (readdata == 32'h00000001)
    );

endmodule