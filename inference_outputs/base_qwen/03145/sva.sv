```systemverilog
module test_eval_generic_sva(
    input logic [7:0] data,
    output logic out_bit_def,
    output logic out_bit_ovr
);
    always @(*) begin
        reg [3:0] ones_count;
        ones_count = {data[7], data[6], data[5], data[4], data[3], data[2], data[1], data[0]};
    end

    always @(*) begin
        if(ones_count >= 4) begin
            out_bit_def = 1'b1;
        end else begin
            out_bit_def = 1'b0;
        end

        if(data[4] == 1'b1) begin
            out_bit_ovr = 1'b1;
        end else begin
            out_bit_ovr = 1'b0;
        end
    end

    // Count the number of 1s in the data
    property count_ones;
        @(posedge CLK) disable iff (!RESETn) ones_count == $countones(data);
    endproperty
    count_ones_check: assert property (count_ones);

    // out_bit_def should be 1 if there are 4 or more 1s in data
    property check_out_bit_def;
        @(posedge CLK) disable iff (!RESETn) (ones_count >= 4) |-> out_bit_def == 1'b1;
    endproperty
    check_out_bit_def_check: assert property (check_out_bit_def);

    // out_bit_def should be 0 if there are fewer than 4 1s in data
    property check_out_bit_def_neg;
        @(posedge CLK) disable iff (!RESETn) (ones_count < 4) |-> out_bit_def == 1'b0;
    endproperty
    check_out_bit_def_neg_check: assert property (check_out_bit_def_neg);

    // out_bit_ovr should be 1 if the 5th bit of data is 1
    property check_out_bit_ovr;
        @(posedge CLK) disable iff (!RESETn) (data[4] == 1'b1) |-> out_bit_ovr == 1'b1;
    endproperty
    check_out_bit_ovr_check: assert property (check_out_bit_ovr);

    // out_bit_ovr should be 0 if the 5th bit of data is 0
    property check_out_bit_ovr_neg;
        @(posedge CLK) disable iff (!RESETn) (data[4] == 1'b0) |-> out_bit_ovr == 1'b0;
    endproperty
    check_out_bit_ovr_neg_check: assert property (check_out_bit_ovr_neg);

    // out_bit_def and out_bit_ovr should not change if data does not change
    property check_out_bits_stable;
        @(posedge CLK) disable iff (!RESETn) data == data_old |-> out_bit_def == out_bit_def_old && out_bit_ovr == out_bit_ovr_old;
    endproperty
    check_out_bits_stable_check: assert property (check_out_bits_stable) else $error("out_bit_def or out_bit_ovr changed unexpectedly");

    // Save the old values of data, out_bit_def, and out_bit_ovr for the stable check
    reg [7:0] data_old;
    reg out_bit_def_old;
    reg out_bit_ovr_old;
    always @(posedge CLK) begin
        if (!RESETn) begin
            data_old <= 8'b0;
            out_bit_def_old <= 1'b0;
            out_bit_ovr_old <= 1'b0;
        end else begin
            data_old <= data;
            out_bit_def_old <= out_bit_def;
            out_bit_ovr_old <= out_bit_ovr;
        end
    end
endmodule
```