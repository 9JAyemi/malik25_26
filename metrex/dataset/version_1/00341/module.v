
module vending_machine(
    input clk,
    input reset,
    input button_A,
    input button_B,
    input button_C,
    input dispense,
    output product_X_selected,
    output product_Y_selected,
    output product_Z_selected,
    output dispensed
);

    // Define the states
    parameter IDLE = 2'b00;
    parameter PRODUCT_X_SELECTED = 2'b01;
    parameter PRODUCT_Y_SELECTED = 2'b10;
    parameter PRODUCT_Z_SELECTED = 2'b11;
    
    // Define the current state and next state
    reg [1:0] current_state;
    reg [1:0] next_state;
    
    // Define the outputs
    reg product_X_selected_reg;
    reg product_Y_selected_reg;
    reg product_Z_selected_reg;
    reg dispensed_reg;
    
    assign product_X_selected = product_X_selected_reg;
    assign product_Y_selected = product_Y_selected_reg;
    assign product_Z_selected = product_Z_selected_reg;
    assign dispensed = dispensed_reg;
    
    // Define the state transition logic
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    
    // Define the next state logic
    always @(*) begin
        case (current_state)
            IDLE: begin
                if (button_A) begin
                    next_state = PRODUCT_X_SELECTED;
                end else if (button_B) begin
                    next_state = PRODUCT_Y_SELECTED;
                end else if (button_C) begin
                    next_state = PRODUCT_Z_SELECTED;
                end else begin
                    next_state = IDLE;
                end
            end
            PRODUCT_X_SELECTED: begin
                if (button_A) begin
                    next_state = PRODUCT_X_SELECTED;
                end else if (button_B) begin
                    next_state = PRODUCT_Y_SELECTED;
                end else if (button_C) begin
                    next_state = PRODUCT_Z_SELECTED;
                end else if (dispense) begin
                    next_state = IDLE;
                end else begin
                    next_state = PRODUCT_X_SELECTED;
                end
            end
            PRODUCT_Y_SELECTED: begin
                if (button_A) begin
                    next_state = PRODUCT_X_SELECTED;
                end else if (button_B) begin
                    next_state = PRODUCT_Y_SELECTED;
                end else if (button_C) begin
                    next_state = PRODUCT_Z_SELECTED;
                end else if (dispense) begin
                    next_state = IDLE;
                end else begin
                    next_state = PRODUCT_Y_SELECTED;
                end
            end
            PRODUCT_Z_SELECTED: begin
                if (button_A) begin
                    next_state = PRODUCT_X_SELECTED;
                end else if (button_B) begin
                    next_state = PRODUCT_Y_SELECTED;
                end else if (button_C) begin
                    next_state = PRODUCT_Z_SELECTED;
                end else if (dispense) begin
                    next_state = IDLE;
                end else begin
                    next_state = PRODUCT_Z_SELECTED;
                end
            end
        endcase
    end
    
    // Define the output logic
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            product_X_selected_reg <= 0;
            product_Y_selected_reg <= 0;
            product_Z_selected_reg <= 0;
            dispensed_reg <= 0;
        end else begin
            case (next_state)
                PRODUCT_X_SELECTED: begin
                    product_X_selected_reg <= 1;
                    product_Y_selected_reg <= 0;
                    product_Z_selected_reg <= 0;
                end
                PRODUCT_Y_SELECTED: begin
                    product_X_selected_reg <= 0;
                    product_Y_selected_reg <= 1;
                    product_Z_selected_reg <= 0;
                end
                PRODUCT_Z_SELECTED: begin
                    product_X_selected_reg <= 0;
                    product_Y_selected_reg <= 0;
                    product_Z_selected_reg <= 1;
                end
                IDLE: begin
                    product_X_selected_reg <= 0;
                    product_Y_selected_reg <= 0;
                    product_Z_selected_reg <= 0;
                    dispensed_reg <= 0;
                end
            endcase
        end
    end
endmodule