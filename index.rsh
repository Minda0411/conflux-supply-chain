'reach 0.1';

const [ isHand, ROCK, PAPER, SCISSORS ] = makeEnum(3);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (handA, handB) =>
  ((handA + (4 - handB)) % 3);

// assert(winner(ROCK, PAPER) == B_WINS);
// assert(winner(PAPER, ROCK) == A_WINS);
// assert(winner(ROCK, ROCK) == DRAW);

// forall(UInt, handA =>
//   forall(UInt, handB =>
//     assert(isOutcome(winner(handA, handB)))));

// forall(UInt, (hand) =>
//   assert(winner(hand, hand) == DRAW));

const Player = {
  ...hasRandom,
  getHand: Fun([], UInt),
  getPrice: Fun([], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {
  const Alice = Participant('Alice', {
    ...Player,
    wager: UInt, // atomic units of currency
    deadline: UInt, // time delta (blocks/rounds)
  });
  const Bob   = Participant('Bob', {
    ...Player,
    acceptWager: Fun([UInt], Null),
  });
  deploy();

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    });
  };

  Alice.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });
  Alice.publish(wager, deadline)
    .pay(wager);
  commit();

  Bob.only(() => {
    interact.acceptWager(wager);
  });
  Bob.pay(wager)
    .timeout(deadline, () => closeTo(Alice, informTimeout));

  var outcome = 0;
  invariant( balance() == 2 * wager);
  while ( outcome == 0 ) {
    commit();

    Alice.only(() => {
      const _handAlice = interact.getPrice();
      const [_commitAlice, _saltAlice] = makeCommitment(interact, _handAlice);
      const commitAlice = declassify(_commitAlice);
    });
    Alice.publish(commitAlice)
      .timeout(deadline, () => closeTo(Bob, informTimeout));
    commit();

    unknowable(Bob, Alice(_handAlice, _saltAlice));
    Bob.only(() => {
      const handBob = declassify(interact.getHand());
    });
    Bob.publish(handBob)
      .timeout(deadline, () => closeTo(Alice, informTimeout));
    commit();

    Alice.only(() => {
      const saltAlice = declassify(_saltAlice);
      const handAlice = declassify(_handAlice);
    });
    Alice.publish(saltAlice, handAlice)
      .timeout(deadline, () => closeTo(Bob, informTimeout));
    checkCommitment(commitAlice, saltAlice, handAlice);

    //outcome = winner(handAlice, handBob);
    outcome = handBob;
    continue;
  }

  //assert(outcome == A_WINS || outcome == B_WINS);
  transfer(2 * wager).to(Alice);
  commit();

  each([Alice, Bob], () => {
    interact.seeOutcome(outcome);
  });
});
