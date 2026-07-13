module PicoBlaze_OutReg_sva #(
    parameter LOCAL_PORT_ID = 8'h00
) (
    input  logic        clk,
    input  logic        reset,
    input  logic [7:0]  port_id,
    input  logic        write_strobe,
    input  logic [7:0]  out_port,
    input  logic [7:0]  new_out_port,
    input  logic        RegEnable
);

    ///// Reset behavior /////
    // While reset is HIGH, new_out_port must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (new_out_port == 8'h00)
    );

    // On the cycle reset deasserts (HIGH->LOW), new_out_port remains 0.
    reset_fall_keeps_zero: assert property (
        @(posedge clk) $fell(reset) |-> (new_out_port == 8'h00)
    );

    ///// RegEnable decode /////
    // RegEnable equals write_strobe && (port_id == LOCAL_PORT_ID).
    regenable_definition: assert property (
        @(posedge clk) disable iff (reset)
            RegEnable == (write_strobe && (port_id == LOCAL_PORT_ID))
    );

    // If RegEnable is HIGH, write_strobe must be HIGH.
    regenable_requires_strobe: assert property (
        @(posedge clk) disable iff (reset)
            RegEnable |-> (write_strobe == 1'b1)
    );

    // If RegEnable is HIGH, port_id must match LOCAL_PORT_ID.
    regenable_requires_port_match: assert property (
        @(posedge clk) disable iff (reset)
            RegEnable |-> (port_id == LOCAL_PORT_ID)
    );

    ///// Register update semantics /////
    // A valid write updates new_out_port with out_port on the next clock.
    update_on_write_hit: assert property (
        @(posedge clk) disable iff (reset)
            (write_strobe && (port_id == LOCAL_PORT_ID)) |=> (new_out_port == $past(out_port))
    );

    // If there is no valid write in two consecutive cycles, new_out_port holds its value.
    hold_when_no_write_two_cycles: assert property (
        @(posedge clk) disable iff (reset)
            ( !(write_strobe && (port_id == LOCAL_PORT_ID))
              ##1 !(write_strobe && (port_id == LOCAL_PORT_ID)) )
            |-> (new_out_port == $past(new_out_port))
    );

endmodule