module gray_shift_register_assertions (
    input logic       CLK,
    input logic       RST,
    input logic [7:0] data_in,
    input logic       shift,
    input logic       load,
    input logic       select,
    input logic [7:0] shift_reg_out,
    input logic [7:0] counter_out,
    input logic [7:0] final_output
);

    function automatic logic [7:0] gray2bin(input logic [7:0] g);
        begin
            gray2bin[7] = g[7];
            gray2bin[6] = g[7] ^ g[6];
            gray2bin[5] = g[7] ^ g[6] ^ g[5];
            gray2bin[4] = g[7] ^ g[6] ^ g[5] ^ g[4];
            gray2bin[3] = g[7] ^ g[6] ^ g[5] ^ g[4] ^ g[3];
            gray2bin[2] = g[7] ^ g[6] ^ g[5] ^ g[4] ^ g[3] ^ g[2];
            gray2bin[1] = g[7] ^ g[6] ^ g[5] ^ g[4] ^ g[3] ^ g[2] ^ g[1];
            gray2bin[0] = g[7] ^ g[6] ^ g[5] ^ g[4] ^ g[3] ^ g[2] ^ g[1] ^ g[0];
        end
    endfunction

    // Reset clears both gray-coded outputs and the mux output on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) RST |=> (counter_out == 8'h00) && (shift_reg_out == 8'h00) && (final_output == 8'h00)
    );

    // select=1 routes the shift-register gray output to final_output.
    check_final_output_selects_shift: assert property (
        @(posedge CLK) disable iff (RST)
        select |-> (final_output == shift_reg_out)
    );

    // select=0 routes the counter gray output to final_output.
    check_final_output_selects_counter: assert property (
        @(posedge CLK) disable iff (RST)
        !select |-> (final_output == counter_out)
    );

    // The gray counter advances by one binary count each active clock.
    check_counter_increments: assert property (
        @(posedge CLK) disable iff (RST)
        !$past(RST) |-> (gray2bin(counter_out) == (gray2bin($past(counter_out)) + 8'd1))
    );

    // Consecutive counter gray values differ by exactly one bit.
    check_counter_gray_step: assert property (
        @(posedge CLK) disable iff (RST)
        !$past(RST) |-> $onehot(counter_out ^ $past(counter_out))
    );

    // load writes data_in into the shift register on the next cycle.
    check_shift_reg_loads_data: assert property (
        @(posedge CLK) disable iff (RST)
        load |=> (gray2bin(shift_reg_out) == $past(data_in))
    );

    // shift left-shifts the stored shift-register value when load is low.
    check_shift_reg_shifts_left: assert property (
        @(posedge CLK) disable iff (RST)
        (!load && shift) |=> (gray2bin(shift_reg_out) == (gray2bin($past(shift_reg_out)) << 1))
    );

    // With neither load nor shift asserted, the shift-register output holds.
    check_shift_reg_holds_value: assert property (
        @(posedge CLK) disable iff (RST)
        (!load && !shift) |=> (shift_reg_out == $past(shift_reg_out))
    );

endmodule