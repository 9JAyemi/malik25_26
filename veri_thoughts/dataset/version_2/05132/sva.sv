module IF_ID_sva (
    input logic        clk,
    input logic        rst,
    input logic        stall,
    input logic        BJ,
    input logic [31:0] if_pcplus4,
    input logic [31:0] if_instr,
    input logic [31:0] id_pcplus4,
    input logic [31:0] id_instr
);

    // Reset sets id_pcplus4 to 4.
    check_reset_pcplus4: assert property (
        @(posedge clk) rst |-> (id_pcplus4 == 32'd4)
    );

    // Reset sets id_instr to the defined bubble value.
    check_reset_instr: assert property (
        @(posedge clk) rst |-> (id_instr == 32'h0000_0020)
    );

    // Stall or BJ causes pcplus4 capture and bubble insertion.
    check_stall_or_bj_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (stall || BJ) |=> ((id_pcplus4 == $past(if_pcplus4)) &&
                           (id_instr   == 32'h0000_0020))
    );

    // Without stall or BJ, both outputs capture the input values.
    check_normal_capture: assert property (
        @(posedge clk) disable iff (rst)
        !(stall || BJ) |=> ((id_pcplus4 == $past(if_pcplus4)) &&
                            (id_instr   == $past(if_instr)))
    );

endmodule