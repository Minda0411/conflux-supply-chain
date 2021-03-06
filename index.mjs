import { loadStdlib } from '@reach-sh/stdlib';
import * as backend from './build/index.main.mjs';
import { ask, yesno, done } from '@reach-sh/stdlib/ask.mjs';
const stdlib = loadStdlib(process.env);

(async () => {
  const isAlice = await ask(
    `Are you Ingredient Supplier?`,
    yesno
  );
  const who = isAlice ? 'Ingredient Supplier' : 'Manufacturer';

  console.log(`Starting Drug Selling Block Chain! as ${who}`);

  let acc = null;
  const createAcc = await ask(
    `Would you like to create an account? (only possible on devnet)`,
    yesno
  );
  if (createAcc) {
    acc = await stdlib.newTestAccount(stdlib.parseCurrency(1000));
  } else {
    const secret = await ask(
      `What is your account secret?`,
      (x => x)
    );
    acc = await stdlib.newAccountFromSecret(secret);
  }

  let ctc = null;
  const deployCtc = await ask(
    `Do you want to deploy the contract? (y/n)`,
    yesno
  );
  if (deployCtc) {
    ctc = acc.deploy(backend);
    const info = await ctc.getInfo();
    console.log(`The contract is deployed as = ${JSON.stringify(info)}`);
  } else {
    const info = await ask(
      `Please paste the contract information:`,
      JSON.parse
    );
    ctc = acc.attach(backend, info);
  }

  const fmt = (x) => stdlib.formatCurrency(x, 4);
  const getBalance = async () => fmt(await stdlib.balanceOf(acc));

  const before = await getBalance();
  console.log(`Your balance is ${before}`);

  const interact = { ...stdlib.hasRandom };

  interact.informTimeout = () => {
    console.log(`There was a timeout.`);
    process.exit(1);
  };
  if (isAlice) {
    const amt = await ask(
      `How much do you want to set the price?`,
      stdlib.parseCurrency
    );
    interact.wager = amt;
    interact.deadline = { ETH: 10, ALGO: 100, CFX: 1000 }[stdlib.connector];
  } else {
    interact.acceptWager = async (amt) => {
      const accepted = await ask(
        `Do you accept the price of ${fmt(amt)}?`,
        yesno
      );
      if (!accepted) {
        process.exit(0);
      }
    };
  }

  const HAND = ['Rock', 'Paper', 'Scissors'];
  const HANDS = {
    '0': 0, 'R': 0, 'r': 0,
    '1': 1, 'P': 1, 'p': 1,
    '2': 2, 'S': 2, 's': 2,
  };

  interact.getHand = async () => {
    const hand = await ask(`How much will you buy?`, (x) => {
      //const hand = HANDS[x];
      const hand = x;
      if ( hand == null ) {
        throw Error(`Not a valid number ${hand}`);
      }
      return hand;
    });
    console.log(`You buy ${hand} g`);
    return hand;
  };

  interact.getPrice = async () => {
    return 0;
  };

  const OUTCOME = ['Bob wins', 'Draw', 'Alice wins'];
  interact.seeOutcome = async (outcome) => {
    //const total = amt * outcome;
    //console.log(`The outcome is: ${OUTCOME[outcome]}`);
    console.log(`Manufacturer buy ${outcome}g from Supplier`);
  };

  const part = isAlice ? backend.Alice : backend.Bob;
  await part(ctc, interact);

  const after = await getBalance();
  console.log(`Your balance is now ${after}`);

  done();
})();