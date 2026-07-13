module traffic_light_fsm_sva (
    input logic       clk,
    input logic       reset,
    input logic       NSG_LED,
    input logic       EWG_LED,
    input logic       yellow_LED,
    input logic [1:0] state_reg,
    input logic [5:0] count
);

    localparam logic [1:0] NSG        = 2'b00;
    localparam logic [1:0] NSG_YELLOW = 2'b01;
    localparam logic [1:0] EWG        = 2'b10;
    localparam logic [1:0] EWG_YELLOW = 2'b11;

    // Reset forces the FSM into NSG.
    check_reset_state_nsg: assert property (
        @(posedge clk) reset |=> (state_reg == NSG)
    );

    // After reset, the NSG output pattern is driven.
    check_reset_outputs_nsg: assert property (
        @(posedge clk) reset |=> (NSG_LED == 1'b1 && EWG_LED == 1'b0 && yellow_LED == 1'b0)
    );

    // NSG lights only the north-south green LED.
    check_nsg_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG) |-> (NSG_LED == 1'b1 && EWG_LED == 1'b0 && yellow_LED == 1'b0)
    );

    // NSG_YELLOW lights only the yellow LED.
    check_nsg_yellow_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG_YELLOW) |-> (NSG_LED == 1'b0 && EWG_LED == 1'b0 && yellow_LED == 1'b1)
    );

    // EWG lights only the east-west green LED.
    check_ewg_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG) |-> (NSG_LED == 1'b0 && EWG_LED == 1'b1 && yellow_LED == 1'b0)
    );

    // EWG_YELLOW lights only the yellow LED.
    check_ewg_yellow_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG_YELLOW) |-> (NSG_LED == 1'b0 && EWG_LED == 1'b0 && yellow_LED == 1'b1)
    );

    // NSG transitions to NSG_YELLOW when count reaches 30.
    check_nsg_timeout_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG && count == 6'd30) |=> (state_reg == NSG_YELLOW && count == 6'd0)
    );

    // NSG holds state and increments count before 30.
    check_nsg_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG && count != 6'd30) |=> (state_reg == NSG && count == ($past(count) + 6'd1))
    );

    // NSG_YELLOW transitions to EWG when count reaches 5.
    check_nsg_yellow_timeout_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG_YELLOW && count == 6'd5) |=> (state_reg == EWG && count == 6'd0)
    );

    // NSG_YELLOW holds state and increments count before 5.
    check_nsg_yellow_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == NSG_YELLOW && count != 6'd5) |=> (state_reg == NSG_YELLOW && count == ($past(count) + 6'd1))
    );

    // EWG transitions to EWG_YELLOW when count reaches 20.
    check_ewg_timeout_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG && count == 6'd20) |=> (state_reg == EWG_YELLOW && count == 6'd0)
    );

    // EWG holds state and increments count before 20.
    check_ewg_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG && count != 6'd20) |=> (state_reg == EWG && count == ($past(count) + 6'd1))
    );

    // EWG_YELLOW transitions to NSG when count reaches 5.
    check_ewg_yellow_timeout_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG_YELLOW && count == 6'd5) |=> (state_reg == NSG && count == 6'd0)
    );

    // EWG_YELLOW holds state and increments count before 5.
    check_ewg_yellow_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == EWG_YELLOW && count != 6'd5) |=> (state_reg == EWG_YELLOW && count == ($past(count) + 6'd1))
    );

endmodule