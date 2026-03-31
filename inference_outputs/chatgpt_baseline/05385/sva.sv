module memory_module_assertions (
    input logic [4:0] A1ADDR,
    input logic       A1DATA,
    input logic       A1EN,
    input logic       CLK1,
    input logic [4:0] B1ADDR,
    input logic       B1DATA,
    input logic [31:0] mem
);

    // Clock is CLK1; there is no reset in the RTL.

    // Read data always reflects the selected memory bit.
    check_read_data_matches_mem: assert property (
        @(posedge CLK1) B1DATA == mem[B1ADDR]
    );

    // With write enable low, the memory contents hold.
    check_no_write_holds_mem: assert property (
        @(posedge CLK1) !A1EN |=> $stable(mem)
    );

    // A write updates memory exactly at the addressed bit.
    check_write_updates_full_mem_state: assert property (
        @(posedge CLK1)
        A1EN |=> mem == (($past(mem) & ~(32'h1 << $past(A1ADDR))) |
                         ({31'b0, $past(A1DATA)} << $past(A1ADDR)))
    );

    // A write stores A1DATA into the addressed location.
    check_write_updates_addressed_bit: assert property (
        @(posedge CLK1) A1EN |=> mem[$past(A1ADDR)] == $past(A1DATA)
    );

    // A write does not change any unaddressed memory bits.
    check_write_preserves_unaddressed_bits: assert property (
        @(posedge CLK1)
        A1EN |=> (((mem ^ $past(mem)) & ~(32'h1 << $past(A1ADDR))) == 32'h0)
    );

    // Writing the existing value leaves memory unchanged.
    check_same_value_write_keeps_mem_stable: assert property (
        @(posedge CLK1) (A1EN && (A1DATA == mem[A1ADDR])) |=> $stable(mem)
    );

    // A subsequent read of the written address returns the stored data.
    check_read_after_write_same_address: assert property (
        @(posedge CLK1)
        A1EN |=> ((B1ADDR != $past(A1ADDR)) || (B1DATA == $past(A1DATA)))
    );

endmodule

bind memory_module memory_module_assertions memory_module_assertions_inst (
    .A1ADDR(A1ADDR),
    .A1DATA(A1DATA),
    .A1EN(A1EN),
    .CLK1(CLK1),
    .B1ADDR(B1ADDR),
    .B1DATA(B1DATA),
    .mem(mem)
);