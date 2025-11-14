// SVA for digital_lock — bindable checker focusing on quality and concise completeness

module digital_lock_sva (
  input  logic [3:0] code,
  input  logic       open,
  input  logic       state,
  input  logic       password_bit,
  input  logic [7:0] sum,
  input  logic [3:0] password
);

  // Sanity: no X/Z on key signals when they change
  assert property (@(code or state or password_bit or sum or open)
                   !$isunknown({code, state, password_bit, sum, open}))
    else $error("X/Z detected on interface or key internal signals");

  // Password is constant and correct
  assert property (@(password) password === 4'b0001)
    else $error("Password modified from 4'b0001");

  // Mux correctness (password_bit selection) after state/password activity
  assert property (@(state or password)
                   1 |-> ##0 (password_bit == (state ? password[0] : password[1])))
    else $error("password_bit mux mismatch");

  // Adder correctness (sum) after inputs to it change
  assert property (@(code or password_bit)
                   1 |-> ##0 (sum == {4'b0, code} + {4'b0, password_bit}))
    else $error("sum calculation mismatch");

  // Output decode correctness: open follows sum zero after sum updates
  assert property (@(sum) 1 |-> ##0 (open == (sum == 8'd0)))
    else $error("open does not match zero-detect of sum");

  // State control: toggle on code==0 event (after NBA), hold otherwise
  assert property (@(code) (code == 4'd0) |-> ##0 $changed(state))
    else $error("state failed to toggle on code==0 event");
  assert property (@(code) (code != 4'd0) |-> ##0 $stable(state))
    else $error("state changed without code==0 event");
  assert property (@(state) $changed(state) |-> (code == 4'd0))
    else $error("state changed without concurrent code==0");

  // Functional equivalences for fixed password (0001)
  // sum==0 <=> code==0 && state==0; open mirrors that
  assert property (@(sum or code or state)
                   ((sum == 8'd0) == ((code == 4'd0) && (state == 1'b0))))
    else $error("sum==0 equivalence with (code==0 && state==0) violated");
  assert property (@(code or state or open)
                   open == ((code == 4'd0) && (state == 1'b0)))
    else $error("open functional condition (code==0 && state==0) violated");

  // Coverage
  cover property (@(code) (code == 4'd0) ##0 $rose(state));
  cover property (@(code) (code == 4'd0) ##0 $fell(state));
  cover property (@(sum)  (sum == 8'd0) ##0 open);
  cover property (@(state) (state==1) ##0 (password_bit==1));
  cover property (@(state) (state==0) ##0 (password_bit==0));

endmodule

// Bind into the DUT to observe internals without modifying the RTL
bind digital_lock digital_lock_sva sva_digital_lock (
  .code(code),
  .open(open),
  .state(state),
  .password_bit(password_bit),
  .sum(sum),
  .password(password)
);