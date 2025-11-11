
module dff_async_reset_set (
    input        clk,
    input        reset_b,
    input        set_b,
    output reg   q
);

    // Register inputs
    reg reset_b_reg;
    reg set_b_reg;

    // Synchronize inputs to the clock
    always @(posedge clk)
    begin
        reset_b_reg <= reset_b;
        set_b_reg   <= set_b;
    end

    // Implement the flip-flop logic
    always @(posedge clk) // fix: control over clocked behavior
    begin
        if (reset_b_reg == 1)
            q <= 0;
        else if (set_b_reg == 1)
            q <= 1;
        else
            q <= q ^ 1;
    end

endmodule