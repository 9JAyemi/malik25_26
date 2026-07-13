module Create_assertions (
    input logic Init,
    input logic creaenhe,
    input logic [6:0] D,
    input logic rst,
    input logic RS,
    input logic RW,
    input logic [6:0] Out_display,
    input logic MsbOD,
    input logic clk,
    input logic [2:0] scrinit
);

    // After a reset cycle, MsbOD and Out_display are cleared.
    check_reset_clears_outputs: assert property (
        @(negedge clk)
        $past(rst) |-> (MsbOD == 1'b0 && Out_display == 7'b0000000)
    );

    // Every non-reset cycle drives RW low.
    check_rw_low_after_active_cycle: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst)) |-> (RW == 1'b0)
    );

    // scrinit 001 drives the first fixed command.
    check_scrinit_001_command: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) && ($past(scrinit) == 3'b001)) |-> (
            Out_display == 7'b0111000 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // scrinit 010 drives the second fixed command.
    check_scrinit_010_command: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) && ($past(scrinit) == 3'b010)) |-> (
            Out_display == 7'b0000100 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // scrinit 011 drives the third fixed command.
    check_scrinit_011_command: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) && ($past(scrinit) == 3'b011)) |-> (
            Out_display == 7'b0001100 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // scrinit 100 drives the fourth fixed command.
    check_scrinit_100_command: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) && ($past(scrinit) == 3'b100)) |-> (
            Out_display == 7'b0000001 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // scrinit 101 drives the fifth fixed command.
    check_scrinit_101_command: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) && ($past(scrinit) == 3'b101)) |-> (
            Out_display == 7'b0110000 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // Default scrinit with creaenhe high drives the create pattern.
    check_default_creaenhe_branch: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) &&
         (($past(scrinit) == 3'b000) || ($past(scrinit) == 3'b110) || ($past(scrinit) == 3'b111)) &&
         $past(creaenhe)) |-> (
            Out_display == 7'b1101110 &&
            MsbOD == 1'b1 &&
            RS == 1'b1
        )
    );

    // Default scrinit with Init high drives the init command.
    check_default_init_branch: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) &&
         (($past(scrinit) == 3'b000) || ($past(scrinit) == 3'b110) || ($past(scrinit) == 3'b111)) &&
         !$past(creaenhe) &&
         $past(Init)) |-> (
            Out_display == 7'b0000001 &&
            MsbOD == 1'b0 &&
            RS == 1'b0
        )
    );

    // Default scrinit with creaenhe low and Init low passes D through.
    check_default_data_branch: assert property (
        @(negedge clk) disable iff (rst)
        (!$past(rst) &&
         (($past(scrinit) == 3'b000) || ($past(scrinit) == 3'b110) || ($past(scrinit) == 3'b111)) &&
         !$past(creaenhe) &&
         !$past(Init)) |-> (
            Out_display == $past(D) &&
            MsbOD == 1'b0 &&
            RS == 1'b1
        )
    );

endmodule