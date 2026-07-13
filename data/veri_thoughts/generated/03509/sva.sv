module EHRU_3_sva #(
    parameter DATA_SZ = 1
) (
    input logic                CLK,
    input logic [DATA_SZ-1:0]  read_0,
    input logic [DATA_SZ-1:0]  write_0,
    input logic                EN_write_0,
    input logic [DATA_SZ-1:0]  read_1,
    input logic [DATA_SZ-1:0]  write_1,
    input logic                EN_write_1,
    input logic [DATA_SZ-1:0]  read_2,
    input logic [DATA_SZ-1:0]  write_2,
    input logic                EN_write_2
);

    // read_1 forwards write_0 when enabled, otherwise exposes read_0.
    check_read1_bypass: assert property (
        @(posedge CLK) read_1 == (EN_write_0 ? write_0 : read_0)
    );

    // read_2 forwards write_1 when enabled, otherwise exposes read_1.
    check_read2_bypass: assert property (
        @(posedge CLK) read_2 == (EN_write_1 ? write_1 : read_1)
    );

    // read_0 is the registered result of the full write-priority chain.
    check_register_next_state: assert property (
        @(posedge CLK)
        1'b1 |=> (read_0 == $past(EN_write_2 ? write_2 :
                                  (EN_write_1 ? write_1 :
                                  (EN_write_0 ? write_0 : read_0))))
    );

    // Port 2 has highest priority for the next stored value.
    check_write2_priority: assert property (
        @(posedge CLK) EN_write_2 |=> (read_0 == $past(write_2))
    );

    // Port 1 supplies the next stored value when port 2 is not writing.
    check_write1_priority: assert property (
        @(posedge CLK) (!EN_write_2 && EN_write_1) |=> (read_0 == $past(write_1))
    );

    // Port 0 supplies the next stored value when higher-priority ports are idle.
    check_write0_priority: assert property (
        @(posedge CLK) (!EN_write_2 && !EN_write_1 && EN_write_0) |=> (read_0 == $past(write_0))
    );

    // The stored value holds when no write enables are asserted.
    check_hold_no_write: assert property (
        @(posedge CLK) (!EN_write_2 && !EN_write_1 && !EN_write_0) |=> (read_0 == $past(read_0))
    );

endmodule