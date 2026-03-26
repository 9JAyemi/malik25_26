module keypad_scanner_sva (
    input logic       clk,
    input logic [3:0] col,
    input logic [3:0] row
);

    // Column 1110 drives row 1110 on the following cycle.
    check_row_for_col_1110: assert property (
        @(posedge clk) (col == 4'b1110) |=> (row == 4'b1110)
    );

    // Column 1101 drives row 1101 on the following cycle.
    check_row_for_col_1101: assert property (
        @(posedge clk) (col == 4'b1101) |=> (row == 4'b1101)
    );

    // Column 1011 drives row 1011 on the following cycle.
    check_row_for_col_1011: assert property (
        @(posedge clk) (col == 4'b1011) |=> (row == 4'b1011)
    );

    // Column 0111 drives row 0111 on the following cycle.
    check_row_for_col_0111: assert property (
        @(posedge clk) (col == 4'b0111) |=> (row == 4'b0111)
    );

    // Any non-matching column value drives row to 0000 on the following cycle.
    check_row_default_for_other_cols: assert property (
        @(posedge clk)
        !((col == 4'b1110) ||
          (col == 4'b1101) ||
          (col == 4'b1011) ||
          (col == 4'b0111)) |=> (row == 4'b0000)
    );

    // Row only takes values produced by the case statement.
    check_row_legal_values: assert property (
        @(posedge clk) 1'b1 |=> (
            (row == 4'b1110) ||
            (row == 4'b1101) ||
            (row == 4'b1011) ||
            (row == 4'b0111) ||
            (row == 4'b0000)
        )
    );

endmodule