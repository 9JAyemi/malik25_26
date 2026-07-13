module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift_amount,
    input logic [15:0] out,
    input logic        clk
);

    function automatic [15:0] rotl16;
        input [15:0] data;
        input [3:0]  sh;
        begin
            case (sh)
                4'h0: rotl16 = data;
                4'h1: rotl16 = {data[14:0], data[15]};
                4'h2: rotl16 = {data[13:0], data[15:14]};
                4'h3: rotl16 = {data[12:0], data[15:13]};
                4'h4: rotl16 = {data[11:0], data[15:12]};
                4'h5: rotl16 = {data[10:0], data[15:11]};
                4'h6: rotl16 = {data[9:0],  data[15:10]};
                4'h7: rotl16 = {data[8:0],  data[15:9]};
                4'h8: rotl16 = {data[7:0],  data[15:8]};
                4'h9: rotl16 = {data[6:0],  data[15:7]};
                4'hA: rotl16 = {data[5:0],  data[15:6]};
                4'hB: rotl16 = {data[4:0],  data[15:5]};
                4'hC: rotl16 = {data[3:0],  data[15:4]};
                4'hD: rotl16 = {data[2:0],  data[15:3]};
                4'hE: rotl16 = {data[1:0],  data[15:2]};
                4'hF: rotl16 = {data[0],    data[15:1]};
                default: rotl16 = 16'h0000;
            endcase
        end
    endfunction

    // The output matches the sampled input rotated by the sampled shift amount after two clocks.
    check_two_cycle_pipeline_rotation: assert property (
        @(posedge clk)
        1'b1 |-> ##2 out == rotl16($past(in, 2), $past(shift_amount, 2))
    );

    // A sampled zero shift returns the sampled input two clocks later.
    check_zero_shift_case: assert property (
        @(posedge clk)
        (shift_amount == 4'h0) |-> ##2 out == $past(in, 2)
    );

    // A sampled shift of one rotates the sampled MSB into bit 0 two clocks later.
    check_shift_one_case: assert property (
        @(posedge clk)
        (shift_amount == 4'h1) |-> ##2 out == {$past(in[14:0], 2), $past(in[15], 2)}
    );

    // A sampled shift of eight swaps the sampled upper and lower bytes two clocks later.
    check_shift_eight_case: assert property (
        @(posedge clk)
        (shift_amount == 4'h8) |-> ##2 out == {$past(in[7:0], 2), $past(in[15:8], 2)}
    );

    // A sampled shift of fifteen rotates sampled bit 0 into bit 15 two clocks later.
    check_shift_fifteen_case: assert property (
        @(posedge clk)
        (shift_amount == 4'hF) |-> ##2 out == {$past(in[0], 2), $past(in[15:1], 2)}
    );

    // A sampled zero input remains zero after the two-cycle pipeline delay.
    check_zero_input_preserved: assert property (
        @(posedge clk)
        (in == 16'h0000) |-> ##2 out == 16'h0000
    );

    // A sampled all-ones input remains all ones after the two-cycle pipeline delay.
    check_all_ones_input_preserved: assert property (
        @(posedge clk)
        (in == 16'hFFFF) |-> ##2 out == 16'hFFFF
    );

endmodule