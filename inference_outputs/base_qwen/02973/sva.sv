module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    output logic [3:0] count
);
    reg [3:0] count_reg;
    reg [3:0] count_next;

    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0000;
        end else begin
            count_reg <= count_next;
        end
    end

    always @* begin
        if (load) begin
            count_next = count;
        end else if (up_down) begin
            count_next = count_reg + 4'b0001;
        end else begin
            count_next = count_reg - 4'b0001;
        end
    end

    always @* begin
        count = count_reg;
    end

    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!reset) count_reg == 4'b0000
    );

    ///// Load behavior /////
    // When load is asserted, the counter should hold its current value.
    load_behavior: assert property (
        @(posedge clk) disable iff (!reset) (load |-> count_reg == count)
    );

    ///// Up count behavior /////
    // When up_down is asserted, the counter should increment.
    up_count_behavior: assert property (
        @(posedge clk) disable iff (!reset) (up_down |-> count_reg == count_next)
    );

    ///// Down count behavior /////
    // When up_down is not asserted, the counter should decrement.
    down_count_behavior: assert property (
        @(posedge clk) disable iff (!reset) (!up_down |-> count_reg == count_next)
    );

    ///// Count value range /////
    // The counter should not exceed 15 or go below 0.
    count_range: assert property (
        @(posedge clk) disable iff (!reset) (count_reg inside {[0:15]})
    );

    ///// Count value stability /////
    // The count value should not change between clock edges unless explicitly updated.
    count_stability: assert property (
        @(posedge clk) disable iff (!reset) (count_reg == count_next)
    );

    ///// Load and up_down cannot be asserted simultaneously /////
    // Load and up_down cannot be asserted simultaneously.
    load_up_down_exclusive: assert property (
        @(posedge clk) disable iff (!reset) !(load && up_down)
    );

    ///// Count value should be consistent with count_reg /////
    // The count value should be consistent with count_reg.
    count_consistency: assert property (
        @(posedge clk) disable iff (!reset) (count == count_reg)
    );

    ///// Count value should not change during reset /////
    // The count value should not change during reset.
    count_during_reset: assert property (
        @(posedge clk) disable iff (reset) count_reg == count
    );

    ///// Count value should not change during load /////
    // The count value should not change during load.
    count_during_load: assert property (
        @(posedge clk) disable iff (load) count_reg == count
    );

    ///// Count value should not change during up_count /////
    // The count value should not change during up_count.
    count_during_up_count: assert property (
        @(posedge clk) disable iff (up_down) count_reg == count
    );

    ///// Count value should not change during down_count /////
    // The count value should not change during down_count.
    count_during_down_count: assert property (
        @(posedge clk) disable iff (!up_down) count_reg == count
    );
endmodule