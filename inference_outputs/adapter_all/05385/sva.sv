module memory_module_sva (
    input logic [4:0] A1ADDR,
    input logic A1DATA,
    input logic A1EN,
    input logic CLK1,
    input logic [4:0] B1ADDR,
    input logic B1DATA
);

    // B1DATA reflects the value stored at B1ADDR on the previous clock.
    check_b1data_matches_previous_memory: assert property (
        @(posedge CLK1) disable iff ($initstate)
        B1DATA == $past(mem[B1ADDR])
    );

    // A write to A1ADDR with A1EN high updates the memory on the next clock.
    check_write_updates_memory: assert property (
        @(posedge CLK1) disable iff ($initstate)
        (A1EN && (A1ADDR == B1ADDR)) |=> mem[B1ADDR] == $past(A1DATA)
    );

    // A write to a different memory address does not change the targeted B1DATA.
    check_write_to_other_address_ignores_b1data: assert property (
        @(posedge CLK1) disable iff ($initstate)
        (A1EN && (A1ADDR != B1ADDR)) |=> B1DATA == $past(B1DATA)
    );

    // Without an enabled write to B1ADDR, B1DATA holds its value.
    check_no_write_holds_b1data: assert property (
        @(posedge CLK1) disable iff ($initstate)
        (!A1EN || (A1ADDR != B1ADDR)) |=> B1DATA == $past(B1DATA)
    );

    // A write to B1ADDR with A1DATA equal to the previous B1DATA leaves B1DATA unchanged.
    check_write_same_value_keeps_b1data: assert property (
        @(posedge CLK1) disable iff ($initstate)
        (A1EN && (A1ADDR == B1ADDR) && (A1DATA == $past(B1DATA))) |=> B1DATA == $past(B1DATA)
    );

    // A write to B1ADDR with A1DATA different from the previous B1DATA changes B1DATA.
    check_write_different_value_changes_b1data: assert property (
        @(posedge CLK1) disable iff ($initstate)
        (A1EN && (A1ADDR == B1ADDR) && (A1DATA != $past(B1DATA))) |=> B1DATA != $past(B1DATA)
    );

endmodule