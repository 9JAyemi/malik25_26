// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): always_ff, counter_increment, assert, property, disable, iff, error, did, not, increment, on, clock, edge, counter_reset, converter_positive, correct, s, complement, for, positive, magnitude, converter_negative, b1, negative, functional_output_select, Functional, match, when, is, high, functional_output_convert, low, functional_output_reset
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .signed_mag(signed_mag),
    .select(select),
    .q(q),
    .binary_counter(binary_counter),
    .counter(counter),
    .count(count),
    .signed_mag_to_twos_comp(signed_mag_to_twos_comp),
    .converter(converter),
    .twos_comp(twos_comp),
    .counter_out(counter_out),
    .converter_out(converter_out),
    .functional_out(functional_out),
    .posedge(posedge),
    .begin(begin),
    .if(if),
    .b0(b0),
    .end(end),
    .else(else),
    .assign(assign),
    .Counter(counter),
    .Converter(converter)
);
