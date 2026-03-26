module d_latch_async_reset (
    input wire D,
    input wire RESET,
    output reg Q
);

    always @(D, RESET)
    begin
        if (RESET == 1'b1)
            Q <= 1'b0;
        else
            Q <= D;
    end

endmodule