// SVA for password_protected_system
// Bind this into the DUT; focuses on correctness, bounds, X-safety, and key functional intent.

bind password_protected_system password_protected_system_sva sva ();

module password_protected_system_sva;

  // Bring DUT scope signals into this bound module
  // (These hierarchical references are valid inside the bound instance)
  logic                clk;
  logic                d;
  logic [255:0]        password;
  logic [2:0]          sel;
  logic [2:0]          shift_reg;
  logic [2:0]          shift_mux_sel;
  logic                shift_mux_out;
  logic [7:0]          password_mux_sel;
  logic [2:0]          password_mux_out;
  logic [2:0]          comparator_out;
  logic [7:0]          shifted_password_mux_sel;
  logic [2:0]          shifted_password_mux_out;
  logic                out;

  // Drive locals from DUT hierarchical names
  assign clk =            password_protected_system.clk;
  assign d =              password_protected_system.d;
  assign password =       password_protected_system.password;
  assign sel =            password_protected_system.sel;
  assign shift_reg =      password_protected_system.shift_reg;
  assign shift_mux_sel =  password_protected_system.shift_mux_sel;
  assign shift_mux_out =  password_protected_system.shift_mux_out;
  assign password_mux_sel = password_protected_system.password_mux_sel;
  assign password_mux_out = password_protected_system.password_mux_out;
  assign comparator_out = password_protected_system.comparator_out;
  assign shifted_password_mux_sel = password_protected_system.shifted_password_mux_sel;
  assign shifted_password_mux_out = password_protected_system.shifted_password_mux_out;
  assign out =            password_protected_system.out;

  default clocking cb @(posedge clk); endclocking

  // Shift register pipeline behavior
  assert property (!$isunknown($past(d))            |-> shift_reg[0] == $past(d))
    else $error("shift_reg[0] mismatch with past d");
  assert property (!$isunknown($past(shift_reg[0])) |-> shift_reg[1] == $past(shift_reg[0]))
    else $error("shift_reg[1] mismatch with past shift_reg[0]");
  assert property (!$isunknown($past(shift_reg[1])) |-> shift_reg[2] == $past(shift_reg[1]))
    else $error("shift_reg[2] mismatch with past shift_reg[1]");

  // Selector encodings
  assert property (shift_mux_sel == {1'b0, sel[1:0]})
    else $error("shift_mux_sel encoding mismatch");
  assert property (password_mux_sel == {1'b0, sel[1:0]})
    else $error("password_mux_sel encoding mismatch");
  assert property (shifted_password_mux_sel == {5'b0, 3'b000})
    else $error("shifted_password_mux_sel should be 0 (constant)");

  // Prevent out-of-range access on shift_reg (index 3 is illegal)
  assert property (shift_mux_sel inside {[0:2]})
    else $error("shift_mux_sel==%0d out of range (will index shift_reg out-of-bounds)", shift_mux_sel);

  // Shift mux correctness per select
  assert property ((shift_mux_sel==0) |-> (shift_mux_out === shift_reg[0]))
    else $error("shift_mux_out mismatch for sel==0");
  assert property ((shift_mux_sel==1) |-> (shift_mux_out === shift_reg[1]))
    else $error("shift_mux_out mismatch for sel==1");
  assert property ((shift_mux_sel==2) |-> (shift_mux_out === shift_reg[2]))
    else $error("shift_mux_out mismatch for sel==2");

  // Password mux downsizing behavior (1-bit read into 3-bit bus)
  assert property (password_mux_sel[7:3]==5'b0)
    else $error("password_mux_sel[7:3] must be 0");
  assert property (password_mux_out[2:1]==2'b00)
    else $error("password_mux_out[2:1] must be 0 (width-mismatch effect)");
  assert property (password_mux_out[0] === password[password_mux_sel])
    else $error("password_mux_out[0] must equal selected password bit");

  // Shifted password mux: constant select -> always password[0], width-downsize
  assert property (shifted_password_mux_out[2:1]==2'b00)
    else $error("shifted_password_mux_out[2:1] must be 0 (width-mismatch effect)");
  assert property (shifted_password_mux_out[0] === password[0])
    else $error("shifted_password_mux_out[0] must equal password[0]");

  // Comparator behavior (3-bit net carrying 1-bit compare)
  assert property (comparator_out[2:1]==2'b00)
    else $error("comparator_out[2:1] must be 0 (width-mismatch effect)");
  assert property (comparator_out[0] === (shift_mux_out == password_mux_out))
    else $error("comparator_out[0] must equal equality result");

  // Output is LSB AND of the two 3-bit buses (higher bits are zeros)
  assert property (out === (comparator_out[0] & shifted_password_mux_out[0]))
    else $error("out must be comparator_out[0] & shifted_password_mux_out[0]");

  // X-safety: no X on index-dependent signals when indices are in-range and inputs known
  assert property ((shift_mux_sel inside {[0:2]}) & !$isunknown(shift_reg) |-> !$isunknown(shift_mux_out))
    else $error("shift_mux_out is X with valid select");
  assert property (!$isunknown({password, password_mux_sel}) |-> !$isunknown(password_mux_out[0]))
    else $error("password_mux_out[0] is X with known inputs");
  assert property (!$isunknown({comparator_out[0], shifted_password_mux_out[0]}) |-> !$isunknown(out))
    else $error("out is X with known inputs");

  // Functional invariance: sel[2] is unused (toggling it alone changes nothing at next sample)
  assert property ($stable({d,password,sel[1:0]}) && $changed(sel[2]) |=> 
                   $stable({shift_mux_sel,password_mux_sel,shift_mux_out,password_mux_out,comparator_out,shifted_password_mux_out,out}))
    else $error("sel[2] affected outputs, but should be unused");

  // Coverage
  cover property (shift_mux_sel==0);
  cover property (shift_mux_sel==1);
  cover property (shift_mux_sel==2);
  cover property (comparator_out[0]==1'b0);
  cover property (comparator_out[0]==1'b1);
  cover property (out==1'b1);

  // Illegal select value (will also trip the range assertion)
  cover property (shift_mux_sel==3);

endmodule