// SVA checker for oam
module oam_chk (
  input  logic        clock,
  input  logic [7:0]  data_a,
  input  logic [7:0]  data_b,
  input  logic [7:0]  address_a,
  input  logic [7:0]  address_b,
  input  logic        wren_a,
  input  logic        wren_b,
  input  logic [7:0]  q_a,
  input  logic [7:0]  q_b
);
  default clocking cb @(posedge clock); endclocking

  bit past_valid;
  logic [7:0] model_a [0:255];
  logic [7:0] model_b [0:255];
  bit         valid_a [0:255];
  bit         valid_b [0:255];

  always_ff @(posedge clock) begin
    past_valid <= 1'b1;
    if (wren_a) begin
      model_a[address_a] <= data_a;
      valid_a[address_a] <= 1'b1;
    end
    if (wren_b) begin
      model_b[address_b] <= data_b;
      valid_b[address_b] <= 1'b1;
    end
  end

  // Synchronous read: q_* reflects the pre-write memory value (no write-through)
  property a_read_beh;
    disable iff (!past_valid)
    valid_a[$past(address_a)] |-> (q_a == $past(model_a[$past(address_a)]));
  endproperty
  assert property (a_read_beh);

  property b_read_beh;
    disable iff (!past_valid)
    valid_b[$past(address_b)] |-> (q_b == $past(model_b[$past(address_b)]));
  endproperty
  assert property (b_read_beh);

  // Coverage: write then hold address -> data visible on q next cycle
  cover property (past_valid && wren_a && $stable(address_a) ##1 (q_a == $past(data_a)));
  cover property (past_valid && wren_b && $stable(address_b) ##1 (q_b == $past(data_b)));
endmodule

bind oam oam_chk oam_chk_i(
  .clock     (clock),
  .data_a    (data_a),
  .data_b    (data_b),
  .address_a (address_a),
  .address_b (address_b),
  .wren_a    (wren_a),
  .wren_b    (wren_b),
  .q_a       (q_a),
  .q_b       (q_b)
);