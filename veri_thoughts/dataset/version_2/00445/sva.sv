module interstage_buffer_if_id_sva (
    input logic       clock,
    input logic [3:0] if_control_signals,
    input logic [3:0] id_control_signals
);

    // id_control_signals captures if_control_signals on the previous rising edge.
    check_control_transfer: assert property (
        @(posedge clock) 1'b1 |=> (id_control_signals == $past(if_control_signals))
    );

endmodule