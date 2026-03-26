module jt51_sh_sva #(parameter width=5, stages=32) (
    input logic                 clk,
    input logic [width-1:0]     din,
    input logic [width-1:0]     drop
);

genvar i;
generate
    for (i=0; i < width; i=i+1) begin : gen_bit_checks
        // Each output bit is the corresponding input bit delayed by stages clocks.
        check_drop_is_stages_cycle_delayed: assert property (
            @(posedge clk) 1'b1 |-> ##stages (drop[i] == $past(din[i], stages))
        );

        // A sustained high input propagates to the output after stages clocks.
        check_high_run_propagates: assert property (
            @(posedge clk) (din[i])[*stages] |=> drop[i]
        );

        // A sustained low input propagates to the output after stages clocks.
        check_low_run_propagates: assert property (
            @(posedge clk) (!din[i])[*stages] |=> !drop[i]
        );
    end
endgenerate

endmodule