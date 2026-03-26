module EHRU_8_sva #(
    parameter DATA_SZ = 1,
    parameter RESET_VAL = 0
) (
    input logic                 CLK,
    input logic [DATA_SZ-1:0]   read_0,
    input logic [DATA_SZ-1:0]   write_0,
    input logic                 EN_write_0,
    input logic [DATA_SZ-1:0]   read_1,
    input logic [DATA_SZ-1:0]   write_1,
    input logic                 EN_write_1,
    input logic [DATA_SZ-1:0]   read_2,
    input logic [DATA_SZ-1:0]   write_2,
    input logic                 EN_write_2,
    input logic [DATA_SZ-1:0]   read_3,
    input logic [DATA_SZ-1:0]   write_3,
    input logic                 EN_write_3,
    input logic [DATA_SZ-1:0]   read_4,
    input logic [DATA_SZ-1:0]   write_4,
    input logic                 EN_write_4,
    input logic [DATA_SZ-1:0]   read_5,
    input logic [DATA_SZ-1:0]   write_5,
    input logic                 EN_write_5,
    input logic [DATA_SZ-1:0]   read_6,
    input logic [DATA_SZ-1:0]   write_6,
    input logic                 EN_write_6,
    input logic [DATA_SZ-1:0]   read_7,
    input logic [DATA_SZ-1:0]   write_7,
    input logic                 EN_write_7
);

    // read_1 forwards write_0 when enabled, else read_0.
    check_read1_mux: assert property (
        @(posedge CLK) read_1 == (EN_write_0 ? write_0 : read_0)
    );

    // read_2 forwards write_1 when enabled, else read_1.
    check_read2_mux: assert property (
        @(posedge CLK) read_2 == (EN_write_1 ? write_1 : read_1)
    );

    // read_3 forwards write_2 when enabled, else read_2.
    check_read3_mux: assert property (
        @(posedge CLK) read_3 == (EN_write_2 ? write_2 : read_2)
    );

    // read_4 forwards write_3 when enabled, else read_3.
    check_read4_mux: assert property (
        @(posedge CLK) read_4 == (EN_write_3 ? write_3 : read_3)
    );

    // read_5 forwards write_4 when enabled, else read_4.
    check_read5_mux: assert property (
        @(posedge CLK) read_5 == (EN_write_4 ? write_4 : read_4)
    );

    // read_6 forwards write_5 when enabled, else read_5.
    check_read6_mux: assert property (
        @(posedge CLK) read_6 == (EN_write_5 ? write_5 : read_5)
    );

    // read_7 forwards write_6 when enabled, else read_6.
    check_read7_mux: assert property (
        @(posedge CLK) read_7 == (EN_write_6 ? write_6 : read_6)
    );

    // read_7 reflects the highest-priority enabled write among ports 0 through 6.
    check_read7_priority_chain: assert property (
        @(posedge CLK)
        read_7 == (
            EN_write_6 ? write_6 :
            EN_write_5 ? write_5 :
            EN_write_4 ? write_4 :
            EN_write_3 ? write_3 :
            EN_write_2 ? write_2 :
            EN_write_1 ? write_1 :
            EN_write_0 ? write_0 : read_0
        )
    );

    // The registered state captured into read_0 follows the full write-priority chain.
    check_next_read0_priority_chain: assert property (
        @(posedge CLK)
        1'b1 |=> read_0 == $past(
            EN_write_7 ? write_7 :
            EN_write_6 ? write_6 :
            EN_write_5 ? write_5 :
            EN_write_4 ? write_4 :
            EN_write_3 ? write_3 :
            EN_write_2 ? write_2 :
            EN_write_1 ? write_1 :
            EN_write_0 ? write_0 : read_0
        )
    );

    // A write on port 7 overrides all earlier stages for the next read_0 value.
    check_write7_overrides_next_state: assert property (
        @(posedge CLK)
        EN_write_7 |=> read_0 == $past(write_7)
    );

endmodule