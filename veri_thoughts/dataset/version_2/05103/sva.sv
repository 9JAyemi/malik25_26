module Counter_sva #(
    parameter int width = 1,
    parameter logic [width - 1 : 0] init = '0
) (
    input logic CLK,
    input logic RST,
    input logic [width - 1 : 0] Q_OUT,
    input logic [width - 1 : 0] DATA_A,
    input logic ADDA,
    input logic [width - 1 : 0] DATA_B,
    input logic ADDB,
    input logic [width - 1 : 0] DATA_C,
    input logic SETC,
    input logic [width - 1 : 0] DATA_F,
    input logic SETF
);

    // Reset loads the counter to init.
    check_reset_loads_init: assert property (
        @(posedge CLK) RST |=> (Q_OUT == init)
    );

    // SETF has highest non-reset priority and loads DATA_F.
    check_setf_loads_data_f: assert property (
        @(posedge CLK) disable iff (RST)
        SETF |=> (Q_OUT == $past(DATA_F))
    );

    // SETC loads DATA_C when SETF is low.
    check_setc_loads_data_c: assert property (
        @(posedge CLK) disable iff (RST)
        !SETF && SETC |=> (Q_OUT == $past(DATA_C))
    );

    // ADDA adds DATA_A when no higher-priority control is active.
    check_adda_updates_counter: assert property (
        @(posedge CLK) disable iff (RST)
        !SETF && !SETC && ADDA |=> (Q_OUT == ($past(Q_OUT) + $past(DATA_A)))
    );

    // ADDB adds DATA_B when no higher-priority control is active.
    check_addb_updates_counter: assert property (
        @(posedge CLK) disable iff (RST)
        !SETF && !SETC && !ADDA && ADDB |=> (Q_OUT == ($past(Q_OUT) + $past(DATA_B)))
    );

    // Without reset or controls, the counter holds its value.
    check_holds_without_controls: assert property (
        @(posedge CLK) disable iff (RST)
        !SETF && !SETC && !ADDA && !ADDB |=> (Q_OUT == $past(Q_OUT))
    );

endmodule