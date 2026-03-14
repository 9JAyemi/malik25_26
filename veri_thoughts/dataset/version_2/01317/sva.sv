module EHRU_7_sva #(
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
    input logic                EN_write_2,
    input logic [DATA_SZ-1:0]  read_3,
    input logic [DATA_SZ-1:0]  write_3,
    input logic                EN_write_3,
    input logic [DATA_SZ-1:0]  read_4,
    input logic [DATA_SZ-1:0]  write_4,
    input logic                EN_write_4,
    input logic [DATA_SZ-1:0]  read_5,
    input logic [DATA_SZ-1:0]  write_5,
    input logic                EN_write_5,
    input logic [DATA_SZ-1:0]  read_6,
    input logic [DATA_SZ-1:0]  write_6,
    input logic                EN_write_6
);

    ///// Cascaded select/passthrough between adjacent read stages /////
    // read_1 selects write_0 when EN_write_0 is HIGH.
    sel_read1_when_en0: assert property (
        @(posedge CLK) EN_write_0 |-> (read_1 == write_0)
    );
    // read_1 passes read_0 when EN_write_0 is LOW.
    pass_read1_when_en0_low: assert property (
        @(posedge CLK) !EN_write_0 |-> (read_1 == read_0)
    );

    // read_2 selects write_1 when EN_write_1 is HIGH.
    sel_read2_when_en1: assert property (
        @(posedge CLK) EN_write_1 |-> (read_2 == write_1)
    );
    // read_2 passes read_1 when EN_write_1 is LOW.
    pass_read2_when_en1_low: assert property (
        @(posedge CLK) !EN_write_1 |-> (read_2 == read_1)
    );

    // read_3 selects write_2 when EN_write_2 is HIGH.
    sel_read3_when_en2: assert property (
        @(posedge CLK) EN_write_2 |-> (read_3 == write_2)
    );
    // read_3 passes read_2 when EN_write_2 is LOW.
    pass_read3_when_en2_low: assert property (
        @(posedge CLK) !EN_write_2 |-> (read_3 == read_2)
    );

    // read_4 selects write_3 when EN_write_3 is HIGH.
    sel_read4_when_en3: assert property (
        @(posedge CLK) EN_write_3 |-> (read_4 == write_3)
    );
    // read_4 passes read_3 when EN_write_3 is LOW.
    pass_read4_when_en3_low: assert property (
        @(posedge CLK) !EN_write_3 |-> (read_4 == read_3)
    );

    // read_5 selects write_4 when EN_write_4 is HIGH.
    sel_read5_when_en4: assert property (
        @(posedge CLK) EN_write_4 |-> (read_5 == write_4)
    );
    // read_5 passes read_4 when EN_write_4 is LOW.
    pass_read5_when_en4_low: assert property (
        @(posedge CLK) !EN_write_4 |-> (read_5 == read_4)
    );

    // read_6 selects write_5 when EN_write_5 is HIGH.
    sel_read6_when_en5: assert property (
        @(posedge CLK) EN_write_5 |-> (read_6 == write_5)
    );
    // read_6 passes read_5 when EN_write_5 is LOW.
    pass_read6_when_en5_low: assert property (
        @(posedge CLK) !EN_write_5 |-> (read_6 == read_5)
    );

    ///// Collapsed passthrough to read_0 when no prior enables are set /////
    // With EN_write_1..0 LOW, read_2 equals read_0.
    no_en_1_to_0_read2_eq_read0: assert property (
        @(posedge CLK) (!EN_write_1 && !EN_write_0) |-> (read_2 == read_0)
    );
    // With EN_write_2..0 LOW, read_3 equals read_0.
    no_en_2_to_0_read3_eq_read0: assert property (
        @(posedge CLK) (!EN_write_2 && !EN_write_1 && !EN_write_0) |-> (read_3 == read_0)
    );
    // With EN_write_3..0 LOW, read_4 equals read_0.
    no_en_3_to_0_read4_eq_read0: assert property (
        @(posedge CLK) (!EN_write_3 && !EN_write_2 && !EN_write_1 && !EN_write_0) |-> (read_4 == read_0)
    );
    // With EN_write_4..0 LOW, read_5 equals read_0.
    no_en_4_to_0_read5_eq_read0: assert property (
        @(posedge CLK) (!EN_write_4 && !EN_write_3 && !EN_write_2 && !EN_write_1 && !EN_write_0) |-> (read_5 == read_0)
    );
    // With EN_write_5..0 LOW, read_6 equals read_0.
    no_en_5_to_0_read6_eq_read0: assert property (
        @(posedge CLK) (!EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && !EN_write_1 && !EN_write_0) |-> (read_6 == read_0)
    );

endmodule