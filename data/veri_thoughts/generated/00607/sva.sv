module BufferCC_sva (
    input logic io_mainClk,
    input logic io_dataIn,
    input logic io_dataOut,
    input logic buffers_0,
    input logic buffers_1
);
    ///// Structural mapping /////
    // io_dataOut is a wire driven by buffers_1.
    check_output_maps_to_buffer1: assert property (
        @(posedge io_mainClk) (io_dataOut == buffers_1)
    );

    ///// Sequential update rules /////
    // buffers_0 captures io_dataIn on each rising edge (1-cycle delay).
    check_buffer0_captures_input: assert property (
        @(posedge io_mainClk) 1 |=> (buffers_0 == $past(io_dataIn))
    );

    // buffers_1 captures buffers_0 on each rising edge (1-cycle delay).
    check_buffer1_captures_buffer0: assert property (
        @(posedge io_mainClk) 1 |=> (buffers_1 == $past(buffers_0))
    );

    ///// Composed pipeline relations /////
    // io_dataOut reflects buffers_0 from the previous cycle.
    check_output_follows_buffer0_one_cycle: assert property (
        @(posedge io_mainClk) 1 |=> (io_dataOut == $past(buffers_0))
    );

    // io_dataOut reflects io_dataIn from two cycles earlier.
    check_output_follows_input_two_cycles: assert property (
        @(posedge io_mainClk) 1 |=> 1 |=> (io_dataOut == $past(io_dataIn,2))
    );

    // buffers_1 reflects io_dataIn from two cycles earlier.
    check_buffer1_follows_input_two_cycles: assert property (
        @(posedge io_mainClk) 1 |=> 1 |=> (buffers_1 == $past(io_dataIn,2))
    );
endmodule